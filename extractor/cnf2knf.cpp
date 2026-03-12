#include "cnf2knf.hpp"
#include "direct_AMO.hpp"
#include "encoded_AMO.hpp"
#include "encoded_blocking_ALK.hpp"
#include <string>
#include <algorithm>
#include <sstream>
#include <iterator>
#include <iostream>
#include <csignal>
#include <atomic>
#include <unistd.h> 
#include <iomanip>

namespace cnf2knf {

using namespace std;

Cnf_extractor* g_cnf_extractor = nullptr;
std::vector<Extraction_engine*>* g_extraction_engines = nullptr;
volatile sig_atomic_t g_got_signal = 0;

// forward declaration so the signal handler can call it
void process_stats(Cnf_extractor * cnf_extractor, std::vector<Extraction_engine*> extraction_engines);


}

extern "C" void cnf2knf_terminate_handler(int sig) {
    using namespace cnf2knf;
    g_got_signal = sig;
    if (g_cnf_extractor) {
        if (g_extraction_engines) {
            // best-effort call to print stats on termination
            process_stats(g_cnf_extractor, *g_extraction_engines);

            // write KNF
            if (g_cnf_extractor->extractor_options["Write_KNF"] != "false")
                g_cnf_extractor->write_knf_formula();
        } else {
            std::vector<Extraction_engine*> empty;
            process_stats(g_cnf_extractor, empty);
        }
    }
    _exit(128 + sig);
}

// ...existing code...

namespace cnf2knf {


string vector2string (vector<int> v) {
    string s;
    for (auto i : v) s += to_string(i) + " ";
    return s;
}

string literals2str (vector<int> literals) {
    string s;
    for (auto l : literals) s += to_string(l) + " ";
    return s;
}

vector<int> flatten_vectors (vector<vector<int>> & clauses) {
    vector<int> res;
    for (auto clause : clauses) {
        for (auto lit : clause) {
            res.push_back (lit);
        }
        res.push_back (0);
    }
    return res;
}

// BDD-based verification of candidate constraint
bool Cnf_extractor::validate_constraint (vector<int> &problem_variables, vector<int> &encoding_variables,  vector<int> &clause_ids, vector<int> &bdd_ordering) {
   // normalize variables and clauses
   vector<vector<int>> normalized_clauses;
   vector<int> literals;
   unordered_map<int,int> to_normalization;
   unordered_map<int,int> from_normalization;

   vector<int> norm_ordering;

   int nproblem = problem_variables.size ();
   int nvar = 1;
   int nKlauses = 0;
   
   for (auto var : problem_variables) {
       to_normalization[var] = nvar++;
       from_normalization[nvar-1] = var;
   }
   for (auto var : encoding_variables) {
       to_normalization[var] = nvar++;
       from_normalization[nvar-1] = var;
   }
   for (auto cls_idx : clause_ids) {
       assert (!clauses[cls_idx].deleted);
       literals.clear ();
       for (auto lit : clauses[cls_idx].literals) {
          if (to_normalization.find (abs(lit)) == to_normalization.end ())
            cout << "Error: literal " << lit << " not in problem or encoding variables" << endl;
           assert (to_normalization.find (abs(lit)) != to_normalization.end ());
           literals.push_back ((abs(lit)/lit) * to_normalization[abs(lit)]);
       }
       normalized_clauses.push_back (literals);
   }
   nvar--;

   // normal bdd_ordering if present
   if (bdd_ordering.size() > 0) {
        for (auto var : bdd_ordering) {
            assert (to_normalization.find (abs(var)) != to_normalization.end ());
            norm_ordering.push_back ((abs(var)/var) * to_normalization[abs(var)]);
        }
   }

   //logging
   string temp_s;
   temp_s = "Problem variables : " + vector2string(problem_variables);
   log_ex_comment (temp_s, 1);
   temp_s = "encoding variables : " +  vector2string(encoding_variables);
   log_ex_comment (temp_s, 1);
   log_ex_comment ("clauses : ", 3);
   for (auto literals : normalized_clauses) {
       temp_s = "";
       for (auto lit : literals) temp_s += to_string ((abs(lit)/lit) * from_normalization[abs(lit)]) + " ";
       temp_s += "0";
       log_ex_comment (temp_s, 3);
   }


   temp_s = "Input Ordering: ";
   for (auto i : norm_ordering) 
    temp_s += to_string(from_normalization[i]) + " ";
   log_ex_comment (temp_s, 2);
   
   // calls bdd_analyze
   analyzed_klauses.clear();
   log_ex_comment ("Entering bdd_analyze", 2);
   // cout << "BDD_analyze " << nvar << " " << nproblem << endl;
   nKlauses = bdd_analyze (nvar, nproblem, normalized_clauses, norm_ordering, from_normalization);
   log_ex_comment ("Exiting bdd_analyze", 2);

   // adds klause if success
   if (nKlauses > 0) { // found valid klause(s)
       
       // add klauses
       for (auto klause : analyzed_klauses) {
           // map literals in klause back to original labelling
          //  cout << "c k add ";
           for (int i = 0; i < klause.get_size() ; i++) {
               int lit = klause.literals[i];
               klause.literals[i] = (abs(lit)/lit) * from_normalization[abs(lit)];
              //  cout << klause.literals[i] << " ";
           }//cout << endl;

           add_klause(klause, clause_ids); // if two klauses will just mark clause_ids deleted twice
  
           nKlauses++;
       stats.bdd_analyze_successes += 1;
       }

   } else { // failed 
//    cout << "Failed" << endl;
       stats.bdd_analyze_failures += 1;
   }

   return (nKlauses > 0);

}

void Cnf_extractor::mark_deleted_clauses (vector<int> clause_ids) {
    for (int cls_id : clause_ids) clauses[cls_id].deleted = true;
}

void Cnf_extractor::extract_direct () {
  return;
}

void Cnf_extractor::init () {

    this->logging = stoi (extractor_options["Extractor_logging"]); 

}

void print_help () {
    cout << "usage: .\\cnf2knf [options] <CNF_FORMULA>" << endl;
    cout << "-h : print this message" << endl;
    cout << "****" << endl;
    cout << " Options set to a value:" << endl;
    cout << "-Encoded_ALK_timeout <float>      (default 1000s)" << endl;
    cout << "-Extractor_logging <int>      (default 0)" << endl;
    cout << "-Engine_logging <int>         (default 0)" << endl;
    cout << "-Write_KNF <file>           (default false)" << endl;
    cout << "-verification_type <int>     (default 3, 0 sim, 1 sat, 2 BDD, 3 sim to sat)" << endl;
    cout << "****" << endl;
    cout << " Options set to true or false (--option=true OR --option=false)" << endl;
    cout << "--totalizer_encoding <bool>           (default false)" << endl;
    
}

int Cnf_extractor::main (int argc, char ** argv) {
    int res = 0;

    // Initial options that lead to exit
    if (argc == 2) {
        const char * temp_s = argv[1];
        if (!strcmp (temp_s, "-h")) {
            print_help ();
            return -1;
        }
    }
    parse_options(argc,argv);
    init ();

    // Parse input CNF formula
    char * input_file = argv[argc-1];
    parse_cnf(input_file);

    return res;
}



void Cnf_extractor::write_knf_formula () {

    ofstream knf_file;
    knf_file.open (extractor_options["Write_KNF"]);

    int nClauses_kept = 0;
    for (auto clause : clauses) nClauses_kept += (clause.deleted)?0:1;
    
    // header
    knf_file << "p knf " << nvars << " " << nClauses_kept + klauses.size() << endl;

    // klauses
    for (auto klause : klauses)
        knf_file << "k " << klause.cardinality_bound << " " << literals2str(klause.literals) << "0" << endl;
    // clauses
    for (auto clause : clauses) {
        if (clause.deleted) continue;
        knf_file << literals2str(clause.literals) << "0" << endl;
    }
    knf_file.close ();
}

void process_stats (Cnf_extractor * cnf_extractor, vector<Extraction_engine*> extraction_engines) {
    

    assert (extraction_engines.size() == 4);

    Direct_AMO *d_AMO = (Direct_AMO *) extraction_engines[0];
    Encoded_AMO *e_AMO = (Encoded_AMO *) extraction_engines[1];
    Encoded_AMO *e_other = (Encoded_AMO *) extraction_engines[2];
    Encoded_ALK *e_ALK = (Encoded_ALK *) extraction_engines[3];

    int total_constraints = 0;
    for (auto clause : cnf_extractor->clauses) {
        if (!clause.deleted) total_constraints++;
    }

    int bdd_successes, bdd_failures, total_card_constraints;
    bdd_successes = bdd_failures = total_card_constraints = 0;

    cout << fixed << setprecision(3);

    cout << "c Original Variables: " << cnf_extractor->nvars << endl;
    cout << "c Original constraints: " << cnf_extractor->clauses.size() << endl;

    cout << "c Clausal constraints: " << total_constraints << endl;

    if (d_AMO != NULL) {
        Stats * stats = d_AMO->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Direct AMO constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Direct AMO sizes: " << temp_s << endl;
        }

        cout << "c Direct AMO seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (d_AMO->reached_timeout) cout << "c Direct reached timeout: " << d_AMO->timeout << endl;
    }

    if (e_AMO != NULL) {
        Stats * stats = e_AMO->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Encoded AMO constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Encoded AMO sizes: " << temp_s << endl;

            cout << "c Encoding variables eliminated: " << stats->eliminated_variables.size () << endl ;

            temp_s = "";
            sort (stats->eliminated_variables.begin(), stats->eliminated_variables.end());
            for (auto ev: stats->eliminated_variables) temp_s += to_string (ev) + " ";
            cout << "c Eliminated variables IDs: " << temp_s << endl;

            
        }

        cout << "c Encoded AMO seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (e_AMO->reached_timeout) cout << "c Encoded reached timeout: " << e_AMO->timeout << endl;

        bdd_successes += stats->bdd_analyze_successes;
        bdd_failures += stats->bdd_analyze_failures;
    }

    if (e_other != NULL) {
        Stats * stats = e_other->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c Other constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            string temp_s = "";
            vector<tuple<int,int>> pair_sizes;
            for (auto it = stats->constraint_sizes.begin(); it != stats->constraint_sizes.end(); it++) {
                pair_sizes.push_back (tuple<int,int>{it->first,it->second});
                // cout << it->first << "  " << it->second << endl;
            }
            sort (pair_sizes.begin(), pair_sizes.end(), [](tuple<int,int> l1, tuple<int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : pair_sizes) temp_s += to_string (get<0>(tp)) + ":" + to_string (get<1>(tp)) + " ";

            cout << "c Other constraint sizes: " << temp_s << endl;

            cout << "c Other variables eliminated: " << stats->eliminated_variables.size () << endl ;

            temp_s = "";
            sort (stats->eliminated_variables.begin(), stats->eliminated_variables.end());
            for (auto ev: stats->eliminated_variables) temp_s += to_string (ev) + " ";
            cout << "c Other eliminated variables IDs: " << temp_s << endl;

            
        }

        cout << "c Other constraint seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (e_AMO->reached_timeout) cout << "c Other reached timeout: " << e_AMO->timeout << endl;

        bdd_successes += stats->bdd_analyze_successes;
        bdd_failures += stats->bdd_analyze_failures;
    }

    if (e_ALK != NULL) {
        Stats * stats = e_ALK->stats;
        total_card_constraints += stats->nconstraints;
        cout << "c ALK constraints: " << stats->nconstraints << endl;
        if (stats->nconstraints > 0) {
            int nGeneralALK = 0;
            int nAMOALK = 0;
            string temp_s = "";
            vector<tuple<int,int,int>> alk_sizes;
            for (auto it = stats->ALK_constraint_sizes.begin(); it != stats->ALK_constraint_sizes.end(); it++) {
                alk_sizes.push_back (tuple<int,int,int>{get<0>(it->first),get<1>(it->first),it->second});
                // cout << it->first << "  " << it->second << endl;
                if (get<0>(it->first) - get<1>(it->first) > 1) nGeneralALK += it->second;
                else nAMOALK += it->second;
            }
            sort (alk_sizes.begin(), alk_sizes.end(), [](tuple<int,int,int> l1, tuple<int,int,int> l2) { return get<0>(l1) < get<0>(l2); });
            for (auto tp : alk_sizes) temp_s +="(" + to_string (get<0>(tp)) + "," + to_string (get<1>(tp)) + "):" + to_string (get<2>(tp)) + " ";

            cout << "c ALK sizes: " << temp_s << endl;
            cout << "c ALK general constraints: " << nGeneralALK << endl;
            cout << "c ALK AMO constraints: " << nAMOALK << endl;
            cout << "c ALK variables eliminated: " << stats->eliminated_variables.size () << endl ;
        }

        cout << "c ALK seconds: " << stats->get_final_time () + stats->extra_time << endl;

        if (e_ALK->reached_timeout) cout << "c ALK reached timeout: " << e_ALK->timeout << endl;

        bdd_successes += stats->bdd_analyze_successes;
        bdd_failures += stats->bdd_analyze_failures;

        cout << "c Cache hits verified " << stats->cache_hits_verified << endl;
        cout << "c Cache hits unverified " << stats->cache_hits_unverified << endl;
        cout << "c Cache misses " << stats->cache_misses << endl;
        cout << "c Verification time " << stats->verification_time << endl;
        cout << "c testing verification time " << stats->testing_time << endl;
        cout << "c SAT verification time " << stats->sat_time << endl;
        cout << "c BDD verification time " << stats->bdd_analyze_time << endl;
        cout << "c testing successes " << stats->testing_successes << endl;
        cout << "c testing failures " << stats->testing_failures << endl;
        cout << "c SAT successes " << stats->sat_successes << endl;
        cout << "c SAT failures " << stats->sat_failures << endl;
        cout << "c BDD successes " << stats->bdd_successes << endl;
        cout << "c BDD failures " << stats->bdd_failures << endl;
    }

    cout << "c Total seconds: " << cnf_extractor->stats.get_final_time () 
    << endl;

    cout << "c Total extracted constraints: " << total_card_constraints 
    << endl;

}

void Stats::write_stats() {

    auto end_time = chrono::system_clock::now();
    chrono::duration<double>  total_time = end_time - start_time;

    cout << "c Statistics for cardinality extraction" << endl;
    cout << "c Number eliminated variables " << eliminated_variables.size() << endl;
    cout << "c Total time " << total_time.count() << " seconds" << endl;
}

int run_extraction_engines (Cnf_extractor * cnf_extractor) {
    vector<Extraction_engine*> extraction_engines;
    // expose to signal handler while engines are live
    g_extraction_engines = &extraction_engines;
    Direct_AMO *direct_AMO = NULL;
    Encoded_AMO *encoded_AMO = NULL;
    Encoded_AMO *encoded_Others = NULL;
    Encoded_ALK *encoded_ALK = NULL;
    extraction_engines.push_back (direct_AMO);
    extraction_engines.push_back (encoded_AMO);
    extraction_engines.push_back (encoded_Others);
    extraction_engines.push_back (encoded_ALK);
    double direct_AMO_timeout, encoded_AMO_timeout, encoded_ALK_timeout;
    unordered_map<string, string> engine_options;
    unordered_map<string, string> extractor_options = cnf_extractor->extractor_options;
    int logging = stoi (extractor_options["Engine_logging"]);

    direct_AMO_timeout = encoded_AMO_timeout = encoded_ALK_timeout = 1000;


    if (stof (extractor_options["Direct_timeout"]) > 0 ) {
        direct_AMO_timeout = stof (cnf_extractor->extractor_options["Direct_timeout"] );
    }
    if (stof (extractor_options["Encoded_timeout"]) > 0 )
        encoded_AMO_timeout = stof (cnf_extractor->extractor_options["Encoded_timeout"] );

    if (stof (extractor_options["Encoded_ALK_timeout"]) > 0) {
        encoded_ALK_timeout = stof (cnf_extractor->extractor_options["Encoded_ALK_timeout"]);
    }

    if (extractor_options["Encoded_ALK"] == "true") {
      extractor_options["Direct_AMO"] = "false";
      extractor_options["Encoded_AMO"] = "false";
      extractor_options["Encoded_Others"] = "false";
    }


    if (extractor_options["Encoded_ALK"] == "true") { 

        engine_options["verification_type"] = extractor_options["verification_type"];
        engine_options["second_chance"] = extractor_options["second_chance"];
        engine_options["grid"] = extractor_options["grid"];
        engine_options["ver_only_file"] = extractor_options["ver_only_file"];

        encoded_ALK = new Encoded_ALK (cnf_extractor,logging);
        extraction_engines[3] = encoded_ALK;

        encoded_ALK->init (engine_options);
        encoded_ALK->run (encoded_ALK_timeout); 
        encoded_ALK->stats->set_end_time ();

        // encoded_ALK->clear_data ();  
    }

    if (extractor_options["Direct_AMO"] == "true") { 
        direct_AMO = new Direct_AMO (cnf_extractor,logging);
        // cout << "c find direct AMOS" << endl;
        extraction_engines[0] = direct_AMO;
        direct_AMO->init (engine_options);
        direct_AMO->run (direct_AMO_timeout);  
        direct_AMO->stats->set_end_time ();

        direct_AMO->clear_data ();  
    }



    if (extractor_options["Encoded_AMO"] == "true") { 
        encoded_AMO = new Encoded_AMO (cnf_extractor,logging);
        // cout << "c find encoded AMOS" << endl;
        extraction_engines[1] = encoded_AMO;
        encoded_AMO->init (engine_options);
        encoded_AMO->run (encoded_AMO_timeout);  
        encoded_AMO->stats->set_end_time ();
    }

    double small_time = 0;
    if (extractor_options["Direct_AMO"] == "true" && extractor_options["Direct_AMO_Small"] == "true") { 
        // cout << "c find small direct AMOS" << endl;
        small_time = direct_AMO->find_small_AMOs (); 
        direct_AMO->stats->extra_time = small_time;
    }

    if (extractor_options["Encoded_Others"] == "true") {
        engine_options["AMO"] = "false";
        engine_options["Max_Size"] = "3";
        encoded_Others = new Encoded_AMO (cnf_extractor,logging);
        extraction_engines[2] = encoded_Others;
        encoded_Others->init (engine_options);
        encoded_Others->run (encoded_AMO_timeout);  
        encoded_Others->stats->set_end_time ();
    }

    

    cnf_extractor->stats.set_end_time ();

    process_stats(cnf_extractor, extraction_engines);

    if (extractor_options["Write_KNF"] != "false")
        cnf_extractor->write_knf_formula();

    delete (direct_AMO);
    delete (encoded_AMO);
    delete (encoded_Others);
    delete (encoded_ALK);

    // before returning/cleanup clear global pointer
    g_extraction_engines = nullptr;

    return 0;

}

}



int main (int argc, char ** argv) {
  cnf2knf::Cnf_extractor * cnf_extractor;
  cnf_extractor = new cnf2knf::Cnf_extractor();

  // expose extractor to signal handler
  cnf2knf::g_cnf_extractor = cnf_extractor;

  // install handlers
  std::signal(SIGINT,  cnf2knf_terminate_handler);
  std::signal(SIGTERM, cnf2knf_terminate_handler);
#ifdef SIGALRM
  std::signal(SIGALRM, cnf2knf_terminate_handler);
#endif

  int res;
  res = cnf_extractor->main (argc, argv);
  if (res) return 0;

  cnf2knf::run_extraction_engines (cnf_extractor);

  // clear global pointer before exit
  cnf2knf::g_cnf_extractor = nullptr;

  return res;
}
