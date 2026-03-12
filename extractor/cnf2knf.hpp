#ifndef CNF2KNF_HPP
#define CNF2KNF_HPP

#include <string>
#include <string.h>
#include <vector>
#include <iostream>
#include <chrono>
#include <unordered_map>
#include <map>
#include <set>
#include <algorithm>
#include "assert.h"

#include "klause.hpp"

#include <fstream>
#include <cstdlib> 
#include <random>

#include "cadical.hpp"


namespace cnf2knf {

using namespace std;

typedef tuple<int, int> pair_key;



// hash for unordered map on (int,int) key
struct pair_key_hash //: public unary_function<pair_key, size_t> //
{
 size_t operator()(const pair_key& k) const
 {
   return std::get<0>(k) + std::get<1>(k) * ((int64_t) 2147483647 + 1);
 }
};

// hash for unordered map on (int,int) key
struct vec_key_hash //: public unary_function<pair_key, size_t> //
{
 size_t operator()(const vector<int>& k) const
 {
    int hash = 0;
    for (int i = 0; i < k.size(); i++) hash += i * k[i];
    return hash;
 }
};

// comparison for ordered map
struct compare_pair {
    bool operator()(const pair_key &l1, const pair_key &l2) 
        const {   if (get<0>(l1) < get<0>(l2)) return true;
            if (get<0>(l1) == get<0>(l2)) return (get<1>(l1) < get<1>(l2));
            return false; }
};



class Stats {

    public:

        int cache_hits_verified, cache_hits_unverified;
        int cache_misses;

        int bdd_analyze_failures;
        int bdd_analyze_successes;

        int nconstraints;
        unordered_map<int,int> constraint_sizes;

        unordered_map<tuple<int,int>,int, pair_key_hash> ALK_constraint_sizes;
        
        chrono::system_clock::time_point start_time;
        chrono::system_clock::time_point final_time;

        double extra_time;
        double verification_time;

        double bdd_analyze_time, testing_time, sat_time;

        int testing_successes;
        int testing_failures;
        int sat_successes;
        int sat_failures;
        int bdd_successes;
        int bdd_failures;

        vector<int> eliminated_variables;

        Stats() {
            cache_hits_verified = 0;
            cache_hits_unverified = 0;
            cache_misses = 0;
            bdd_analyze_failures = 0;
            bdd_analyze_successes = 0;

            bdd_successes = 0;
            bdd_failures = 0;

            testing_successes = 0;
            testing_failures = 0;
            sat_successes = 0;
            sat_failures = 0;

            bdd_analyze_time = 0;
            testing_time = 0;
            sat_time = 0;

            verification_time = 0;

            nconstraints = 0;

            extra_time = 0;

            start_time = chrono::system_clock::now();
            
        }

        double get_elapsed_time () {
            auto end_time = chrono::system_clock::now();
            chrono::duration<double>  total_time = end_time - start_time;

            return (total_time.count ());
        }

        double get_final_time () {
            // auto end_time = chrono::system_clock::now();
            chrono::duration<double>  total_time = final_time - start_time;

            return (total_time.count ());
        }

        void set_end_time() {
            final_time = chrono::system_clock::now();
        }

        void write_stats ();

};

class Constraint_cache {
  public : 

  int nHits;
  int nMisses;

  unordered_map<int, tuple<int,int>> var_map;
  unordered_map<int, int> var_map_reverse; 
  int lit_map_stamp;
  vector<int> key;

  unordered_map<vector<int>, tuple<vector<int>,bool,vector<Klause>>, vec_key_hash> constraint_cache;

  Constraint_cache() {
    nHits = 0;
    nMisses = 0;
    lit_map_stamp = 0;
  }

  // normalize and linearize a set of clauses by mapping variables to a canonical form based on their first occurrence in the clauses
  void linearize (vector<int> &clauses) {
    lit_map_stamp++;
    key.clear();
    int var_count = 1;

    for (auto &lit : clauses) {
      if (var_map.find (abs(lit)) == var_map.end()) {
        var_map[abs(lit)] = tuple<int,int>(lit_map_stamp, var_count++);
      } else if (std::get<0>(var_map[abs(lit)]) != lit_map_stamp) {
        var_map[abs(lit)] = tuple<int,int>(lit_map_stamp, var_count++);
      }
      int sign = (lit > 0) ? 1 : -1;
      int next_lit = sign * std::get<1>(var_map[abs(lit)]);
      key.push_back (next_lit);
      var_map_reverse[abs(next_lit)] = abs(lit);
    }
  }

  bool add (vector<int> &clauses , bool success, vector<Klause> klause) {
    linearize (clauses);
    if (constraint_cache.count (key)) {
      return false;
    }
    // map klauses 
    for (auto &kl : klause) {
      for (auto &lit : kl.literals) {
        int sign = (lit > 0) ? 1 : -1;
        lit = sign * std::get<1>(var_map[abs(lit)]);
      }
    }
    constraint_cache[key] = tuple<vector<int>,bool,vector<Klause>>(key, success, klause);
    return true;
  }

  bool get (vector<int> &clauses, bool &success, vector<Klause> &klause) {
    linearize (clauses);
    if (constraint_cache.count (key)) {
      tuple<vector<int>,bool,vector<Klause>> value = constraint_cache[key];
      // check linearized clauses match 
      if (std::get<0>(value) != key) { 
        nMisses++;
        return false;
      }
      nHits++;
      success = std::get<1>(value);
      klause = std::get<2>(value);
      // map the klause literals correctly
      for (auto &kl : klause) {
        for (auto &lit : kl.literals) {
          int sign = (lit > 0) ? 1 : -1;
          lit = sign * var_map_reverse[abs(lit)];
        }
      }
      return true;
    }
    nMisses++;
    return false;
  }
  
};

class Cnf_extractor {

    public:

        int             nvars;   // Number of variables
        vector<Klause>  clauses; // Clauses from original CNF formula
        vector<Klause>  klauses; // All klauses generated during extraction

        unordered_map<string, string> extractor_options;

        int logging;

        vector<Klause>  analyzed_klauses; // Klauses generated in current analyze step

        Stats stats;

        Constraint_cache* constraint_cache;



        Cnf_extractor () {
            // populate options
            extractor_options["Direct_timeout"] = "1000";
            extractor_options["Encoded_timeout"] = "1000"; 
            extractor_options["Encoded_ALK_timeout"] = "1000";
            extractor_options["Extractor_logging"] = "0";
            extractor_options["Engine_logging"] = "0";
            extractor_options["BDD_logging"] = "0";
            extractor_options["Direct_AMO"] = "true";
            extractor_options["Direct_AMO_Small"] = "true";
            extractor_options["Encoded_AMO"] = "true";
            extractor_options["Encoded_Others"] = "false";
            extractor_options["Write_KNF"] = "false";
            extractor_options["Encoded_ALK"] = "true";
            extractor_options["verification_type"] = "3";

            extractor_options["BDD_ordering_file"] = "0";
            extractor_options["aux_var_file"] = "0";
            extractor_options["second_chance"] = "false";
            extractor_options["grid"] = "false";

            extractor_options["ver_only_file"] = "false";

            constraint_cache = new Constraint_cache();
            
            }

        void init ();

        int main (int argc, char ** argv);

        // extract directly encoded AMO constraints
        void extract_direct();

        // Analyze set of clauses with data variables numbered from 1 to ndata
        // and encoding variables numbered from ndata+1 to nvar
        // Return number of klauses generated (0 if failure)
        // Place new klauses into analyzed_klauses 
        //   which will be cleared before each call to bdd_analyze
       int bdd_analyze (int nvar, int ndata, vector<vector<int>> &constraint_clauses, vector<int> & norm_ordering, unordered_map<int, int> &);

       

       bool validate_constraint (vector<int> &problem_variables, vector<int> &encoding_variables,  vector<int> &clause_ids, vector<int> &bdd_ordering);

       bool validate_constraint (vector<int> &problem_variables, vector<int> &encoding_variables,  vector<int> &clause_ids) {
        vector<int> t;
        return (validate_constraint (problem_variables, encoding_variables, clause_ids, t));
       }

        // parsing
        int parse_options (int argc, char ** argv);
        bool findOption(char ** start, char ** end, const string & marker);
        bool commandLineParseOption(char ** start, char ** end, const string & marker);

        int parse_cnf (char *);

        // writing
        void write_knf_formula ();

        void add_klause (Klause klause, vector<int> clause_ids) {
            klauses.push_back (klause);
            mark_deleted_clauses (clause_ids);
        }

        void log_ex_comment (string line, int log_if) {
        if (log_if <= logging) {
            cout << "c " << line << endl; 
        }
    }

        private :

        void mark_deleted_clauses (vector<int> clause_ids);


};

class Extraction_engine {
    public :

    double timeout;
    bool   reached_timeout;
    int logging;

    Cnf_extractor * cnf_extractor;
    Stats * stats;

    Extraction_engine (Cnf_extractor * cnf_extractor, int logging) {
        this->cnf_extractor = cnf_extractor;
        reached_timeout = false;
        this->logging = logging;
    }

    // dictionary containing parameters for initializing this engine
    virtual void init (unordered_map<string, string> engine_options) {};
    
    // start extraction with timeout
    virtual void run (double timeout) {};

    // write stats to standard out
    virtual void write_stats () {};

    void log_comment (string line, int log_if) {
        if (log_if <= logging) {
            cout << "c " << line << endl; 
        }
    }

    
};

struct totalizer_node {
    // A node in the totalizer tree
    // It contains a vector of counters (literals) and pointers to left and right children
    vector<int> counters;
    totalizer_node *left, *right;

    // destructor deletes all children nodes
    ~totalizer_node() {
      if (left) {
        delete left;
      }

      if (right) {
        delete right;
      }
    }
    // Constructors
    totalizer_node() : left(nullptr), right(nullptr) {}
    totalizer_node(vector<int> c) : counters(c), left(nullptr), right(nullptr) {}
    totalizer_node(vector<int> c, totalizer_node *l, totalizer_node *r) 
      : counters(c), left(l), right(r) {}
    totalizer_node(const totalizer_node &other) 
      : counters(other.counters), left(other.left), right(other.right) {}
  };

typedef struct totalizer_node totalizer_node;

class SatSolver {
  public:

  

    CaDiCaL::Solver *solver;
    vector<int> data_vars;
    vector<vector<int>> original_clauses;
    vector<int> original_clause_ids;
    int nvars;
    int bound;
    bool ALK;

    Cnf_extractor *cnf_extractor;

     SatSolver(int nvars, Cnf_extractor *cnf_extractor) {
      bound = -1;
      ALK = false;
      solver = new CaDiCaL::Solver();
      this->cnf_extractor = cnf_extractor;

      int random_seed = 1;
      rng = default_random_engine(random_seed);

      this->nvars = nvars;
    }

    SatSolver(int nvars, vector<int> data_vars, vector<vector<int>> &clauses) {
      bound = -1;
      ALK = false;
      solver = new CaDiCaL::Solver();

      // solver->set("forcephase",1);
      // solver->set("phase",1);

      int random_seed = 1;
      rng = default_random_engine(random_seed);

      this->data_vars = data_vars;
      this->nvars = nvars;
      add_clauses(clauses);
    }

    ~SatSolver() {
      delete solver;
    }

    void set_data_vars(vector<int> data_vars) {
      this->data_vars = data_vars;
    }

    void add_clauses(const vector<vector<int>> &clauses) {
      for (const auto &clause : clauses) {
        add_clause(clause);
        
      }
    }

    void add_clause(const vector<int> &clause) {
      for (int lit : clause) {
        solver->add(lit);
      }
      solver->add(0); // End of clause
      original_clauses.push_back(clause);
    }

    int solve() {
      return solver->solve(); // 10 means SAT
    }

    void add_clauses_directly(vector<vector<int>> &clauses, CaDiCaL::Solver *new_solver) {
      for (const auto &clause : clauses) {
        for (int lit : clause) {
          new_solver->add(lit);
        }
        new_solver->add(0); // End of clause
      }
    }

    bool random_testing_prefilter(int nSAT_simulations = 500, int nUNSAT_simulations = 500, float percent_tight_simulations = 0.5);

    bool verify_with_sat (bool match_tree = false, bool is_scnt = false);

    bool verify_with_BDD ();

    void find_bound_by_simulation ();
    int run_guided_simulation ();
    bool run_simulation(int nTrue, int expected_result);
    void make_simulation_assumptions(int nTrue);

      void build_sequential_counter (vector<int> &data_vars, vector<vector<int>> &clauses, vector<int> &output_lits, int nvars, int bound);

    totalizer_node* build_existing_totalizer_tree(vector<int> data_vars, vector<vector<int>> &clauses, int nvars);

    void build_totalizer_encoding(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars) ;

    bool is_totalizer_leaf (totalizer_node * node);

vector<int> totalizer_mid_variables(int left_size, int right_size, int bound, int &nvars) ;
    
void add_totalizer_node_clauses(totalizer_node *node, int bound, vector<vector<int>> &clauses);

void build_totalizer_encoding_from_existing_tree(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars, totalizer_node * existing_tree) ;

totalizer_node * traverse_existing_tree (totalizer_node* current_node, int &nvars, vector<bool> &used_vars, int ndata_vars, unordered_map<int, int> &data_vars_polarity_map) ;

  private:
    int nSAT_simulations;
    int nUNSAT_simulations;
    float percent_tight_simulations;
    default_random_engine rng;

};



}

#endif
