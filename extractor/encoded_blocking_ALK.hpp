#ifndef ENCODED_BLOCKING_ALK_HPP
#define ENCODED_BLOCKING_ALK_HPP

#include "cnf2knf.hpp"


namespace cnf2knf {

using namespace std;

inline string literals2strP (vector<int> literals) {
    string s;
    for (auto l : literals) s += to_string(l) + " ";
    return s;
}

struct VectorHash {
    size_t operator()(const std::vector<int>& v) const {
        std::hash<int> hasher;
        size_t seed = 0;
        for (int i : v) {
            seed ^= hasher(i) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        }
        return seed;
    }
};

class Encoded_ALK : public Extraction_engine {

    public: 

        unordered_map<int, tuple<int, int>> variable_polarity_map;
        unordered_map<int, vector<int>> encoding_variable_map;
        unordered_map<int, vector<int>> problem_variable_map;

        unordered_map<int, set<int>> lit2clss_occurence_map;

        struct  blocking_set_info {
            int pos_cnt; // blocking set count for positive literal
            int neg_cnt; // blocking set count for negative literal
            int pos_depends; // blocking set dependencies for positive literal
            int neg_depends; // blocking set dependencies for negative literal
            int union_depends; // union of blocking set dependencies for both polarities
            int intersect_depends; // intersection of blocking set dependencies for both polarities
             blocking_set_info() {
                pos_cnt = 0;
                neg_cnt = 0;
                pos_depends = 0;
                neg_depends = 0;
                union_depends = 0;
                intersect_depends = 0;
            }
        };

        vector< blocking_set_info> var_blocking_set_info; 
        unordered_map<vector<int>, int, VectorHash> clause_hash_map;
        unordered_map<int,int> occurs_in_big;

        vector<int> is_unit;

        vector<int> var_type;
        vector<Klause> verified_klauses;
        vector<int> var_used;

        vector<int> var_appears;

        SatSolver *sat_solver;

        int block_set_count_limit, large_clause_size_cutoff;
        bool caching;

        int verification_type;

        unordered_map<string, string> engine_options;

        using Extraction_engine::Extraction_engine;



        void init (unordered_map<string, string> engine_options) {

            // default parameters
            caching = true;
            block_set_count_limit = 100; 
            large_clause_size_cutoff = 4;
            verification_type = stoi (engine_options["verification_type"]); // 0 sim, 1 sat, 2 BDD, 3 sim to sat
            this->engine_options = engine_options;
        }

        void init_solver () {
          sat_solver = new SatSolver(cnf_extractor->nvars, cnf_extractor);
        }

        void cleanup_solver () {
          delete sat_solver;
        }

        void print_variables () {
          string temp_s = "Problem Variables: ";
          for (auto it = problem_variable_set.begin(); it != problem_variable_set.end(); it++) temp_s += to_string (*it) + " ";
          log_comment (temp_s, 1);

          temp_s = "Encoding Variables: ";
          for (auto it = encoding_variable_set.begin(); it != encoding_variable_set.end(); it++) temp_s += to_string (*it) + " ";
          log_comment (temp_s, 1);
        }

        // set phase of problem variables based on binary clauses they appear in
        void set_polarity_problem () {
          for (auto &var : problem_variables) {
            int var_phase = 0;
            bool mixed_phase = false;
            int lowest_clause_id = INT_MAX;
            for (int pol : {-1,1}) {
              for (auto cls_id : lit2clss_occurence_map[var*pol]) {
                if (clause_ids_set.count(cls_id) && cnf_extractor->clauses[cls_id].get_size() == 2) {
                   var_phase = pol;
                   break; 
                  if (var_phase == 0) {
                    var_phase = pol;
                    lowest_clause_id = cls_id;
                  } else if (var_phase != pol) {
                    if (lowest_clause_id > cls_id) {
                      var_phase = pol;
                    }
                  }
                  break;
                }
              }
            }
            if (var_phase == 0) var_phase = 1;
            var = var_phase * abs(var); // default to positive phase
          }
        }

        // random-testing prefilter, SAT-based and BDD-based verification
        bool verify_constraint_int (SatSolver *solver) {
          // add new_clause_ids to solver for random-testing or SAT-based verification
          for (auto id : new_clause_ids_set) {
            solver->add_clause(cnf_extractor->clauses[id].literals);
            solver->original_clause_ids.push_back(id);
          }
          new_clause_ids_set.clear();

          problem_variables.clear();
          encoding_variables.clear();

          problem_variables = vector<int> (problem_variable_set.begin(), problem_variable_set.end());
          encoding_variables = vector<int> (encoding_variable_set.begin(), encoding_variable_set.end());
          
          // guess polarity of data literals
          set_polarity_problem ();

          solver->set_data_vars(problem_variables);

          bool res, bdd;
          bdd = false;

          double start_time = stats->get_elapsed_time();

          if (verification_type == 2) {
            // BDD-based verification
            bdd = true;
            int old_nklauses = cnf_extractor->klauses.size();
            vector<int> pos_data_vars;
            for (auto var : problem_variables) {
              pos_data_vars.push_back(abs(var));
            }

            res = cnf_extractor->validate_constraint (pos_data_vars, encoding_variables, solver->original_clause_ids);

            double end_time = stats->get_elapsed_time();
            stats->bdd_analyze_time += (end_time - start_time);
            if (res) 
              stats->bdd_successes++;
            else
              stats->bdd_failures++;

            if (res) {
              int new_nklauses = cnf_extractor->klauses.size();
              // log the kclause from the BDD location
              // get last new clauses off stack and push
              for (int i = old_nklauses; i < new_nklauses; i++) {
                verified_klauses.push_back(cnf_extractor->klauses[i]);
              }
            }
          } else {
            if (verification_type == 0) {
              // Only random-testing
              res = solver->random_testing_prefilter();
              double end_time = stats->get_elapsed_time();
              stats->testing_time += (end_time - start_time);
              if (res) 
                stats->testing_successes++;
              else
                stats->testing_failures++;
            }
            else if (verification_type == 1) {
              // Only SAT-based verification
              if (engine_options["grid"] == "true") {
                res = solver->verify_with_sat(true, false);
              } else {
                res = solver->verify_with_sat(false, true);
              }
              if (!res) {
                log_comment("SAT solver verification failed", 2);
              }
              double end_time = stats->get_elapsed_time();
              stats->sat_time += (end_time - start_time);
              if (res) 
                stats->sat_successes++;
              else
                stats->sat_failures++;
            } else if (verification_type == 3) {
              // Random-testing prefilter followed by SAT-based verification if it passes the prefilter
              res = solver->random_testing_prefilter();
              double end_time = stats->get_elapsed_time();
              stats->testing_time += (end_time - start_time);
              if (res) 
                stats->testing_successes++;
              else
                stats->testing_failures++;
              if (res) {
                start_time = stats->get_elapsed_time();
                if (engine_options["grid"] == "true") { // totalizer based SAT-verification
                  res = solver->verify_with_sat(true, false);
                } else {
                  res = solver->verify_with_sat(false, true);
                }
                if (!res) {
                  log_comment("SAT solver verification failed", 2);
                }
                double end_time = stats->get_elapsed_time();
                stats->sat_time += (end_time - start_time);
                if (res) 
                  stats->sat_successes++;
                else
                  stats->sat_failures++;
              }
            }

            if (res && !bdd) {
              // add the new klause to the verified clauses list
              vector<int> klause_vars = problem_variables;
              int bound = solver->bound;
              if (!solver->ALK) {
                for (auto &var : klause_vars) {
                  var = -var;  // negate variable for non-ALK clauses
                }
                bound = problem_variables.size() - bound;
              }

              Klause klause(klause_vars, bound);
              verified_klauses.push_back(klause);
            }
          }
          
          return res;
        }

        bool verify_constraint () {
          double start_time = stats->get_elapsed_time();
          bool res = verify_constraint_int (sat_solver);
          double end_time = stats->get_elapsed_time();
          stats->verification_time += (end_time - start_time);
          cout << "c Single verification time " << stats->verification_time << " seconds" << endl;
          return res;
        }

        void add_verified_constraint () {

          problem_variables.clear();
          encoding_variables.clear();

          problem_variables = vector<int> (problem_variable_set.begin(), problem_variable_set.end());
          encoding_variables = vector<int> (encoding_variable_set.begin(), encoding_variable_set.end());

          int csize = problem_variables.size ();
          stats->nconstraints++;
          if (stats->constraint_sizes.find (csize) == stats->constraint_sizes.end ())
              stats->constraint_sizes[csize] = 0;
          stats->constraint_sizes[csize]++;

          // eliminated variables
          // cout << "c k del ";
          for (auto ev : encoding_variables) {
              stats->eliminated_variables.push_back (ev);
              var_used[ev] = 1;
              // cout << ev << " ";
          } //cout << endl;

          for (auto klause : verified_klauses) {
            tuple<int,int> klause_tuple = tuple<int,int>(klause.get_size(), klause.cardinality_bound);
            if (stats->ALK_constraint_sizes.find (klause_tuple) == stats->ALK_constraint_sizes.end ())
              stats->ALK_constraint_sizes[klause_tuple] = 0;
            
            stats->ALK_constraint_sizes[klause_tuple]++;

            cout << "c k " << klause.cardinality_bound << " " << literals2strP(klause.literals) << "0" << endl;

            cnf_extractor->add_klause (klause, vector<int> (clause_ids_set.begin(), clause_ids_set.end()));

          }
          verified_klauses.clear ();
        }

        void print_blocking_counts (vector< blocking_set_info> &var_blocking_set_info) {
          string temp_s = "";
          for (int i = 1; i < var_blocking_set_info.size(); i++) {
            // variable is the index in the vector
            temp_s +=  "c v " + to_string(i) + " p " + to_string(var_blocking_set_info[i].pos_cnt) + " n " + to_string (var_blocking_set_info[i].neg_cnt) +  " p dep " + to_string(var_blocking_set_info[i].pos_depends) + " n dep " + to_string(var_blocking_set_info[i].neg_depends) + " t " + to_string(var_type[i])  + "\n";
          }
          log_comment (temp_s, 2);
        }

        bool compare_blocking_counts ( blocking_set_info a,  blocking_set_info b) {
            int val1, val2;

            val1 = min(a.pos_cnt,a.neg_cnt);
            if (a.pos_cnt == -1)
              val1 = a.neg_cnt;

            val2 = min(b.pos_cnt,b.neg_cnt);
            if (b.pos_cnt == -1)
              val2 = b.neg_cnt;
            
            return val1 < val2;
        }

        bool grid_mode_enabled (int var) {
          return engine_options["grid"] == "true";
        }

        // *******************************************
        // Functions for only verification, no extraction. Used for scaling tests
        void get_touched_clauses () {
          for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
              int var_t = var_type[abs(lit)];
              if (var_t == 1) {
                new_clause_ids_set.insert(cls_idx);
                clause_ids_set.insert(cls_idx);
                break;
              }
            }
          }
        }

        void get_vars (string vFile) {
            cout << "c Get vars from file " << vFile << endl;
            ifstream ordering_file (vFile);
            string s;
            int var;
            bool data_vars = false;
            bool encoding_vars = false;
            if (ordering_file.is_open()) {
              while (ordering_file >> s) {
                // cout << s << endl;
                if (s == "d") {
                  data_vars = true;
                  encoding_vars = false;
                  continue;
                }
                if (s == "e") {
                  data_vars = false;
                  encoding_vars = true;
                  continue;
                }
                var = abs(stoi(s));
                if (data_vars) {
                  problem_variable_set.insert(var);
                  var_type[var] = 2;
                }
                if (encoding_vars) {
                  encoding_variable_set.insert(var);
                  var_type[var] = 1;
                }
              }
              ordering_file.close();
            }
            if (!encoding_vars) {
              for (int var = 1; var <= cnf_extractor->nvars; var++) {
                if (var_type[var] == 0) {
                  encoding_variable_set.insert(var);
                  var_type[var] = 1;
                }
              }
            }
        }

        void verify_only () {
          cout << "c Verify only" << endl;
          init_solver();
          cout << "c get vars" << endl;
          get_vars(engine_options["ver_only_file"]);
          cout << "c get touched clauses" << endl;
          get_touched_clauses();

          // print_variables ();

          cout << "c verify constraint" << endl;
          bool result = verify_constraint ();
          cout << "c Verification result: " << result << endl;
          if (result) add_verified_constraint ();
          cleanup_solver();
        }

        // *******************************************

        void run (double timeout) {

            string temp_s;
            vector<int> aux_vars;
            var_type.resize(cnf_extractor->nvars+1,0);
            var_used.resize(cnf_extractor->nvars+1,0);

            // get blocking clause counts for each variable
              // build occurence list
            get_occurence_maps();

            this->stats = new Stats(); // start clock running
            this->timeout = timeout;

            // no extraction, just verification of a given constraint
            if (engine_options["ver_only_file"] != "false") {
              verify_only();
              return;
            }

            // build clause hash map
            get_clause_hash_map();

            // find blocking set info for each variable
            get_var_blocking_set_info();

            // initial classifiaction of auxilairy and non-auxilairy/data variables
            if (engine_options["grid"] == "true") 
              hier_sort_vars_by_type (aux_vars, var_type);
            else
              grid_sort_vars_by_type (aux_vars, var_type);

            // print blocking set info if logging level is high enough
            print_blocking_counts(var_blocking_set_info);

            // put aux variables in reverse ID order
            sort(aux_vars.begin(), aux_vars.end(), greater<int>());

            cout << "c Start Aux-directed expansions with " << aux_vars.size() << " aux variables and " << cnf_extractor->clauses.size() << " clauses" << endl;

            for (auto var : aux_vars) {
              if (!var_appears[var]) continue;
              if (var_used[var]) continue; // already in an extracted constraint

              // early exit if timelimit reached
              if (stats->get_elapsed_time() > timeout) {
                    stats->set_end_time();
                    reached_timeout = true; 
                    break;
              }

              bool validated = false;
              bool cache_hit = false;

              init_solver();
              
              // perform expansion to obtain a candidate constraint
              if (grid_mode_enabled (var)) {
                extract_totalizer (var);
              } else {
               auxiliary_closure_first (var, var_type);
              }

              // caching for the candidate constraint before verification, to avoid expensive repeated verification of the same constraint
              vector<int> flat_clauses;
              if (caching) {
                bool success;
                vector<Klause> c_klauses;
                for (auto id : clause_ids_set) {
                  for (auto lit : cnf_extractor->clauses[id].literals) 
                    flat_clauses.push_back(lit);
                  flat_clauses.push_back(0);
                }
                if (cnf_extractor->constraint_cache->get(flat_clauses, success, c_klauses)) {
                  if (success) {
                    cout << "c Cache hit" << endl;
                    for (auto kl : c_klauses) {
                      verified_klauses.push_back(kl);
                    }
                    validated = true;
                    cache_hit = true;
                    stats->cache_hits_verified++;
                  } else {
                    cache_hit = true;
                    validated = false;
                    stats->cache_hits_unverified++;
                  }
                } else {
                  stats->cache_misses++;
                }
              }

              // verify constraint if no cache hit and at least 10 data variables.
              if (!validated && !cache_hit && problem_variable_set.size() > 10) {
                validated = verify_constraint ();
              }

              // mark auxiliary variables as seen if they were used during expansion. This happens internally in the grid expansion function
              if (grid_mode_enabled (var) && !validated && !cache_hit) {
                ;
              } else {
                for (auto ev : encoding_variable_set) {
                    var_used[ev] = 1;
                }
              }

              if (validated) {
                if (!cache_hit) { // add to cache for future candidates
                    cnf_extractor->constraint_cache->add(flat_clauses, true, verified_klauses);
                }
                add_verified_constraint ();
              } else {
                if (!cache_hit) { // add to cache for future candidates that are not valid
                    cnf_extractor->constraint_cache->add(flat_clauses, false, vector<Klause>());
                }
              }
              cleanup_solver ();
            }
        }

        void write_stats () {}


    private:
      
    // Initial classification of variables in the hierarchical mode
    void hier_sort_vars_by_type (vector<int> &aux_vars, vector<int> &var_type) {
      for (int var = 1; var <= cnf_extractor->nvars; var++) {
        int val1, val2;
        bool non_aux = false;

        bool definite_problem = false;

        val1 = min(var_blocking_set_info[var].pos_cnt,var_blocking_set_info[var].neg_cnt);
        val2 = max(var_blocking_set_info[var].pos_cnt,var_blocking_set_info[var].neg_cnt);

        // blocking count criteria
        non_aux = !(val1 > 0 && val2 > 0 && val1 <= 2 && val2 <= 6);

        // blocking dependencies criteria
        non_aux = non_aux || (max(var_blocking_set_info[var].pos_depends, var_blocking_set_info[var].neg_depends) > 5);

        // definite problem variable if it appears in a large clause, is exclusively defined, or cannot be blocked
        definite_problem = occurs_in_big.find(var) != occurs_in_big.end() || val1 == 0 || val2 == 0 || val1 == -1 || val2 == -1;

        if (definite_problem) {
          var_type[var] = 3;
        }
        else if (non_aux) {
          var_type[var] = 1;
        } else {
          var_type[var] = 2;
          aux_vars.push_back(var);
        }
      }
    }

    // Initial classification of variables in the grid mode
    void grid_sort_vars_by_type (vector<int> &aux_vars, vector<int> &var_type) {
      for (int var = 1; var <= cnf_extractor->nvars; var++) {
        int val1, val2;
        bool non_aux = false;

        val1 = min(var_blocking_set_info[var].pos_cnt,var_blocking_set_info[var].neg_cnt);
        val2 = max(var_blocking_set_info[var].pos_cnt,var_blocking_set_info[var].neg_cnt);

        if (var_blocking_set_info[var].pos_cnt <= 0) {
          val1 = var_blocking_set_info[var].neg_cnt;
          val2 = var_blocking_set_info[var].pos_cnt;
        }
        else if (var_blocking_set_info[var].neg_cnt <= 0) {
          val1 = var_blocking_set_info[var].pos_cnt;
          val2 = var_blocking_set_info[var].neg_cnt;
        }

        // appears in large clause, is exclusively defined, cannot be blocked, or has too large of a minimum blocking count
        non_aux = non_aux || (val1 > 2 || (val1 <= 0) || (val2 <= 0) || occurs_in_big.find(var) != occurs_in_big.end());

        // // if pure (occurs less with PLE)
        if (lit2clss_occurence_map[var].size() == 0 || lit2clss_occurence_map[-var].size() == 0) {
          non_aux = false;
        }

        // check this after pure check, since pure variables can still be non-aux if they appear in large clauses
        non_aux = non_aux || occurs_in_big.find(var) != occurs_in_big.end();
        // has too many blocking dependencies
        non_aux = non_aux || (max(var_blocking_set_info[var].pos_depends, var_blocking_set_info[var].neg_depends) > 5);

        if (non_aux) {
          var_type[var] = 1;
        } else {
          var_type[var] = 2;
          aux_vars.push_back(var);
        }
      }
    }

    // check if blocking set clause is in the formula using the clause hash map
    bool has_clause (vector<int> lits) {
      sort (lits.begin(), lits.end());
      return clause_hash_map.find (lits) != clause_hash_map.end();
    }

    void get_occurence_maps () {

        is_unit.resize(cnf_extractor->nvars+1,0);
        var_appears.resize(cnf_extractor->nvars+1,0);

        for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                lit2clss_occurence_map[lit].insert (cls_idx);
                var_appears[abs(lit)] = 1;
                if (cnf_extractor->clauses[cls_idx].literals.size() > large_clause_size_cutoff) {
                  occurs_in_big[abs(lit)] = 1;
                }
                if (cnf_extractor->clauses[cls_idx].literals.size() == 1) {
                  is_unit[abs(lit)] = 1;
                }
            }
        }
    }

    void get_clause_hash_map () {
        for (int cls_idx = 0; cls_idx < cnf_extractor->clauses.size(); cls_idx++) {
            // skip deleted clauses
            if (cnf_extractor->clauses[cls_idx].deleted) continue;

            vector<int> lits;

            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                lits.push_back (lit);
            }

            sort (lits.begin(), lits.end());
            clause_hash_map[lits] = 1;
        }
    }

    set<set<int>> blocking_clauses;

    void print_vector (vector<int> v) {
      for (auto i : v) cout << i << " ";
      cout << endl;
    }

    void print_set (set<int> s) {
      for (auto i : s) cout << i << " ";
      cout << endl;
    }

    // Build blocking set iteratively. Avoid sets with repeated literals (would be subsumed) and stop if there are too many blocking clauses.
    int get_blocking_clauses (int lit) {

      blocking_clauses.clear();
      blocking_clauses.insert (set<int>{-lit});

      set<set<int>> blocking_clauses_swap;

      set<int> seen_lits;

      for (auto cls: lit2clss_occurence_map[lit]) {
        bool was_swapped = false;
        for (auto lit2 : cnf_extractor->clauses[cls].literals) {
          if (lit2 == lit) continue;
          if (seen_lits.find (lit2) != seen_lits.end()) continue;

          for (auto partial_cls: blocking_clauses) {
            set<int> blocking_clause;
            blocking_clause = partial_cls;

            // if contains a lit from the blocking clause, skip
            // would be subsumed...
            bool contains = false;
            for (auto lit3: blocking_clause) {
              for (auto lit4 : cnf_extractor->clauses[cls].literals) {
                if (lit4 == lit) continue;
                if (-lit3 == lit4) {
                  contains = true;
                  break;
                }
              }
            }

            if (!contains)
              blocking_clause.insert (-lit2);
            blocking_clauses_swap.insert (blocking_clause);
            was_swapped = true;
          }
        }

        for (auto lit2 : cnf_extractor->clauses[cls].literals) {
          seen_lits.insert (lit2);
        }
        // could avoid swap here 
          if (was_swapped) {
            blocking_clauses.clear();
            for (auto partial_cls: blocking_clauses_swap) {blocking_clauses.insert (partial_cls);}// print_set(partial_cls);}
            blocking_clauses_swap.clear();
          }

          if (blocking_clauses.size() > block_set_count_limit) {
            return -1;
          }
      }

      return 1;
      
    }

    // formula not pure, not blockable
    bool has_lit_both_polarities (int lit) {
      set<int> touched_lits;
      for (auto cls_idx : lit2clss_occurence_map[lit]) {
        for (auto lit2 : cnf_extractor->clauses[cls_idx].literals) {
          if (lit2 == lit) continue;
          if (touched_lits.find (-lit2) != touched_lits.end())
            return true;
          touched_lits.insert (lit2);
        }
      }

      return false;
    }

    int get_blocking_clause_count (int lit, set<int> &depends) {
      int cnt = 0;

      // determine all blocking clauses
      int res =get_blocking_clauses (lit);
      if (res == -1) {
        return block_set_count_limit;
      }

      // unit
      if (blocking_clauses.size() == 1 && (*(blocking_clauses.begin())).size() == 1) {
        return 0;
      }

      // find blocking clause count and dependencies
      for (auto block_cls : blocking_clauses) {
        if (!has_clause(vector<int> (block_cls.begin(), block_cls.end()))) {
          cnt++;
        }
        for (auto l : block_cls) {
          if (abs(l) == abs(lit)) continue;
          depends.insert (abs(l));
        }
      }
      if (lit > 0)
        var_blocking_set_info.back().pos_depends = depends.size();
      else 
        var_blocking_set_info.back().neg_depends = depends.size();
        
      return cnt;
    }

    // literal not pure and formula not pure
    int can_block (int lit) {
      if (lit2clss_occurence_map[lit].size() == 0) 
        return -2; 
      else if (has_lit_both_polarities(lit)) 
        return -1;
      else
      return 1; 
    }

    // Get blocking set information for each variable and store in var_blocking_set_info vector. This includes blocking set counts for both polarities, dependencies, and union and intersection of dependencies.
    void get_var_blocking_set_info () {
      int cnt_pos, cnt_neg;

      blocking_set_info info0;
      info0.pos_cnt = 0;
      info0.neg_cnt = 0;
      var_blocking_set_info.push_back (info0);

      for (int var = 1; var <= cnf_extractor->nvars; var++) {

        blocking_set_info info;
        info.pos_cnt = 0;
        info.neg_cnt = 0;
        info.pos_depends = 0;
        info.neg_depends = 0;
        var_blocking_set_info.push_back (info);

        set<int> depends_pos, depends_neg;
        cnt_pos = can_block (var);
        if (cnt_pos == 1)
          cnt_pos = get_blocking_clause_count (var, depends_pos);

        cnt_neg = can_block (-var);
        if (cnt_neg == 1)
          cnt_neg = get_blocking_clause_count (-var, depends_neg);
        var_blocking_set_info[var].pos_cnt = cnt_pos;
        var_blocking_set_info[var].neg_cnt = cnt_neg;

        if (cnt_pos == block_set_count_limit) var_blocking_set_info[var].pos_depends = block_set_count_limit;
        if (cnt_neg == block_set_count_limit) var_blocking_set_info[var].neg_depends = block_set_count_limit;

        // Intersection and union of depends
        int unionSize = 0;
        int intersectionSize = 0;

        // Count union elements
        for (auto& elem : depends_pos) unionSize++;
        for (auto& elem : depends_neg) {
          if (depends_pos.find(elem) == depends_pos.end()) unionSize++;
        }

        // Count intersection elements
        for (auto& elem : depends_pos) {
          if (depends_neg.find(elem) != depends_neg.end()) intersectionSize++;
        }
        var_blocking_set_info[var].union_depends = unionSize;
        var_blocking_set_info[var].intersect_depends = intersectionSize;
      }
    }

    // Perform closure over all clauses containing auxilairy variables from the set. Add all variables in the closure that are not classified as problem variables to the expanded set, and add all clauses in the closure to the expanded clause set. Skip variables in skip_vars and clauses larger than cls_cutoff, but add variables in those clauses to cls_cutoff_vars for later consideration.
    void auxiliary_closure (int not_exp_t, set<int> &exp_ts, set<int> &not_exp_ts, set<int> & exp_clause_ids, set<int> skip_vars, int cls_cuttoff , set<int> &cls_cutoff_vars) {

      set<int> unsued_exp_ts;
      for (auto var : exp_ts) unsued_exp_ts.insert(var);

      while (unsued_exp_ts.size()) {
        int next_variable = *(unsued_exp_ts.begin());
        unsued_exp_ts.erase(next_variable);

        if (skip_vars.find (next_variable) != skip_vars.end())
          continue;

        if (var_type[next_variable] == not_exp_t) {
          // problem variable
          not_exp_ts.insert(next_variable);
          continue;
        } else {
          // encoding variable
          exp_ts.insert(next_variable);
          for (int nPol = -1; nPol <=1 ; nPol+=2) {
            for (auto cls_idx : lit2clss_occurence_map[nPol*next_variable]) {
              if (cnf_extractor->clauses[cls_idx].deleted) continue;
              // if not already in exp_clause_ids then add cls_idx
              if (exp_clause_ids.find(cls_idx) == exp_clause_ids.end()) {
                exp_clause_ids.insert(cls_idx);
                new_clause_ids_set.insert(cls_idx);
              }
              for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
                int var2 = abs(lit);
                if (var2 == next_variable || not_exp_ts.find(var2) != not_exp_ts.end() || exp_ts.find(var2) != exp_ts.end() || skip_vars.find (var2) != skip_vars.end()) continue;
                if (cnf_extractor->clauses[cls_idx].literals.size() > cls_cuttoff) {
                    cls_cutoff_vars.insert(var2);
                } else {
                  unsued_exp_ts.insert(var2);
                }
              }
            }
          }
        }
      }
    }

    
    // start with an initial auxilairy variable var then expand the cluster based on the transitive closure 
    void auxiliary_closure_first (int var, vector<int> var_type) {

      encoding_variable_set.clear();
      problem_variable_set.clear();
      clause_ids_set.clear();

      encoding_variable_set.insert(var);

      set<int> cuttoff_vars;

      auxiliary_closure ( 1, encoding_variable_set, problem_variable_set, clause_ids_set, set<int>(), 5, cuttoff_vars);
    }

    
    void print_set (set<int> s, string msg) {
      if (msg != "") cout << msg;
      for (auto i : s) cout << i << " ";
      cout << endl << endl;
    }

    // check if variable is a guranteed data variable based on criteria: appears in large clause, or cannot be blocked
    bool guranateed_data (int var) {
      bool res = false;
      res = res || (occurs_in_big.find(var) != occurs_in_big.end());
      res = res || (min(var_blocking_set_info[var].pos_cnt, var_blocking_set_info[var].neg_cnt) == -1);
      return res;
    }

    // check that a vairiable depends on something outside the set of variables and extra depends, if so convert to data variable
    void convert_to_data_variables (set<int> &variables, set<int>&extra_depends, set<int> &data_variables) {
      for (auto var : extra_depends) {
        if (guranateed_data(var)) {
          data_variables.insert(var);
          continue;
        }
        for (int nPol = -1; nPol <=1 ; nPol+=2) {
          for (auto cls_idx : lit2clss_occurence_map[nPol*var]) {
            if (cnf_extractor->clauses[cls_idx].deleted) continue;
            for (auto lit : cnf_extractor->clauses[cls_idx].literals) {
              int var2 = abs(lit);
              if (variables.find(var2) == variables.end() && extra_depends.find(var2) == extra_depends.end()) {
                data_variables.insert(var);
                break;
              }
            }
            if (data_variables.find(var) != data_variables.end()) break;
          }
        }
      }
    }

    // find any additional clauses touched by the auxilairy variables in the closure and add to clause set
    void close_clauses_on_vars (set<int> &vars, set<int> &cls_ids) {
      for (auto var : vars) {
        for (int nPol = -1; nPol <=1 ; nPol+=2) {
          for (auto cls_idx : lit2clss_occurence_map[nPol*var]) {
            if (cnf_extractor->clauses[cls_idx].deleted) continue;
            cls_ids.insert(cls_idx);
          }
        }
      }
    }


    void extract_totalizer (int var) {
      encoding_variable_set.clear();
      clause_ids_set.clear();
      problem_variable_set.clear();

      // Initial expansion to build outline of the tree
      set<int> exp_low_blocking_count_vars, exp_extra_vars, exp_cls_ids, exp_data_vars, exp_aux_vars;
      exp_low_blocking_count_vars.insert(var);
      expand_variables_by_filter (exp_low_blocking_count_vars, "low_block", exp_extra_vars, exp_cls_ids);

      // initial setting 
      for (auto var : exp_low_blocking_count_vars) {
        var_used[var] = 1;
      }

      // fill in internal auxiliary variables of the tree
      close_internal_aux_variables (exp_low_blocking_count_vars, "low_block", exp_extra_vars, exp_cls_ids);
      
      // Convert variables with other dependencies to data variables
      convert_to_data_variables (exp_low_blocking_count_vars, exp_extra_vars, exp_data_vars);

      // create final set of auxilairy variables
      for (auto var : exp_low_blocking_count_vars) {
        if (exp_data_vars.find(var) == exp_data_vars.end()) {
          exp_aux_vars.insert(var);
        }
      }
      for (auto var : exp_extra_vars) {
        if (exp_data_vars.find(var) == exp_data_vars.end()) {
          exp_aux_vars.insert(var);
        }
      }

      // close aux variables to get remaining clause ids 
      close_clauses_on_vars (exp_aux_vars, exp_cls_ids);

      // copy to correct sets for verification
      for (auto var : exp_aux_vars) {
        encoding_variable_set.insert(var);
      }
      for (auto var : exp_data_vars) {
        problem_variable_set.insert(var);
      }
      for (auto cls_idx : exp_cls_ids) {
        clause_ids_set.insert(cls_idx);
        new_clause_ids_set.insert(cls_idx);
      }

    }


    // Perform additional expansion to close internal auxiliary variables in the tree, based on criteria such as touching both positive and negative clauses or touching size 4 clauses, which are common in the kmod totalizer encoding of the modulus function.
    void close_internal_aux_variables (set<int> &variables, string filter_type, set<int> &extra_vars, set<int> &cls_ids) {
      set<int> exp_vars; 
      set<int> blocked_vars;
      for (auto var : extra_vars) {

        int cnt_touched = 0; 
        int nPos_cls = 0, nNeg_cls = 0;
        bool in_size4 = false;
        set<int> touched_vars;
        for (int nPol = -1; nPol <= 1; nPol += 2) {
          int lit = nPol * var;
          if (lit2clss_occurence_map.find(lit) == lit2clss_occurence_map.end()) continue;
          
          for (auto cls_idx : lit2clss_occurence_map[lit]) {
            if (cnf_extractor->clauses[cls_idx].deleted) continue;
            if (cls_ids.find(cls_idx) == cls_ids.end()) continue;

            if (nPol == 1) nPos_cls++;
            else nNeg_cls++;

            if (cnf_extractor->clauses[cls_idx].literals.size() == 4) in_size4 = true;

            for (auto lit2 : cnf_extractor->clauses[cls_idx].literals) {
              int var2 = abs(lit2);
              if (var2 == var) continue;
              if (variables.find(var2) != variables.end()) touched_vars.insert(var2);
              if (extra_vars.find(var2) != extra_vars.end()) touched_vars.insert(var2);
            }
          }
        }
        // pos and neg cls for addeed data variables later in the tree
        // Size 4 special case modulus variable (if comes from high counters)
        if (touched_vars.size() > 3 && ((nPos_cls > 0 && nNeg_cls > 0) || in_size4)) {
          exp_vars.insert(var);
        }
        else {
          blocked_vars.insert(var);
        }
      }

      set<int> expanded_already, new_extra;

      // Now expand the internal auxilairy variables to find other auxilairy variables
      while (exp_vars.size () > 0) {
        int var = *(exp_vars.begin());
        exp_vars.erase(var);
        expanded_already.insert(var);
        if (var_type[var] == 3) continue; // skip if data variable

        // add new vars 
        for (int nPol = -1; nPol <= 1; nPol += 2) {
          int lit = nPol * var;
          if (lit2clss_occurence_map.find(lit) == lit2clss_occurence_map.end()) continue;
          
          for (auto cls_idx : lit2clss_occurence_map[lit]) {
            if (cnf_extractor->clauses[cls_idx].deleted) continue;
            cls_ids.insert(cls_idx);
            
            // Examine all variables in this clause
            for (auto lit2 : cnf_extractor->clauses[cls_idx].literals) {
              int var2 = abs(lit2);
              if (var2 == var || variables.find(var2) != variables.end() || expanded_already.find(var2) != expanded_already.end() || blocked_vars.find(var2) != blocked_vars.end() || exp_vars.find(var2) != exp_vars.end()) continue;
              exp_vars.insert(var2);
              if (extra_vars.find(var2) == extra_vars.end()) {
                extra_vars.insert(var2);
                new_extra.insert(var2);
              }
            }
          }
        }
      }
    }

    // Perform initial expansion to find likely auxiliary variables based on the low blocking count filter, then expand based on other criteria such as touching both positive and negative clauses or touching size 4 clauses, which are common in the kmod totalizer encoding of the modulus function. Add variables that do not pass the filter to extra_vars for later consideration as data variables, and add all touched clauses to cls_ids.
    void expand_variables_by_filter (set<int> &variables, string filter_type, set<int> &extra_vars, set<int> &cls_ids) {
      set<int> to_expand = variables;
      vector<int> to_expand_vec (to_expand.begin(), to_expand.end());

      bool first = true;
      
      while (!to_expand_vec.empty()) {
        set<int> newly_added;
        vector<int> newly_added_vec;
        
        // Iterate through each variable to expand
        for (auto var : to_expand_vec) {
          // Look at all clauses this variable touches (both polarities)
          bool passes_pre_check = true;
          int cnt_touched = 0; 
          for (int nPol = -1; nPol <= 1; nPol += 2) {
            int lit = nPol * var;
            if (lit2clss_occurence_map.find(lit) == lit2clss_occurence_map.end()) continue;
            
            for (auto cls_idx : lit2clss_occurence_map[lit]) {
              if (cnf_extractor->clauses[cls_idx].deleted) continue;
              
              // Examine all variables in this clause
              for (auto lit2 : cnf_extractor->clauses[cls_idx].literals) {
                int var2 = abs(lit2);
                if (var2 == var) continue;
                if (variables.find(var2) != variables.end() || extra_vars.find(var2) != extra_vars.end()) cnt_touched++;
              }
            }
          }
          passes_pre_check = (cnt_touched > 1);

          if (first) {
            passes_pre_check = true; // allow first variable to pass pre check
            first = false;
          }

          if (!passes_pre_check) {
            // for jumping over top of totlaizer 
            if (min(var_blocking_set_info[var].pos_cnt, var_blocking_set_info[var].neg_cnt) <= 1 && min(var_blocking_set_info[var].pos_depends, var_blocking_set_info[var].neg_depends) <= 1) 
              passes_pre_check = true;
          }

          if (!passes_pre_check) {
            extra_vars.insert(var);
            variables.erase(var);
            continue;
          }

          int pos_depends = var_blocking_set_info[var].pos_depends;
          int neg_depends = var_blocking_set_info[var].neg_depends;

          int max_depends = max(pos_depends, neg_depends);
          int min_depends = min(pos_depends, neg_depends);
          int max_polarity = (pos_depends > neg_depends) ? 1 : -1;


          // expand the variable, check all clauses it appears in for other likely auxilairy variables
          for (int nPol = -1; nPol <= 1; nPol += 2) {
            int lit = nPol * var;
            if (lit2clss_occurence_map.find(lit) == lit2clss_occurence_map.end()) continue;
            
            for (auto cls_idx : lit2clss_occurence_map[lit]) {
              if (cnf_extractor->clauses[cls_idx].deleted) continue;

              cls_ids.insert(cls_idx);
              
              // Examine all variables in this clause
              for (auto lit2 : cnf_extractor->clauses[cls_idx].literals) {
                int var2 = abs(lit2);
                if (var2 == var || variables.find(var2) != variables.end()) continue;
                
                // Apply the filter to decide if var2 should be added
                bool passes_filter = false;
                
                if (filter_type == "low_block") {
                    int min_count = min(var_blocking_set_info[var2].pos_cnt, var_blocking_set_info[var2].neg_cnt);
                    passes_filter = (min_count <= 2) && (min_count >= 0);
                } else if (filter_type == "all") {
                  // Add all variables
                  passes_filter = true;
                } else if (filter_type == "encoding_only") {
                  // Add only encoding variables
                  passes_filter = (var_type[var2] != 1);
                } else if (filter_type == "problem_only") {
                  // Add only problem variables
                  passes_filter = (var_type[var2] == 1);
                } 

                // final check for mod variable at top of kmod totalizer...
                if (cnf_extractor->clauses[cls_idx].literals.size() == 4) {
                  passes_filter = true;
                }

                if (var_type[var2] == 3) {
                  // problem variable cannot be likely auxiliary variabble
                  passes_filter = false; 
                }
                
                if (passes_filter) {
                  if ( extra_vars.find(var2) != extra_vars.end()) {
                    extra_vars.erase(var2);
                  }
                  if (newly_added.find(var2) == newly_added.end()) {
                    newly_added_vec.push_back(var2);
                  }
                  newly_added.insert(var2);
                  variables.insert(var2);
                } else {
                  extra_vars.insert(var2);
                }
              }
            }
          }
        }
        
        // Set up for next iteration: only expand newly added variables
        to_expand_vec = newly_added_vec;
  
      }
    }


    int get_block_cnt_pol (int lit) {
      return (lit > 0) ? var_blocking_set_info[abs(lit)].pos_cnt : var_blocking_set_info[abs(lit)].neg_cnt;
    }

    int get_depends_pol (int lit) {
      return (lit > 0) ? var_blocking_set_info[abs(lit)].pos_depends : var_blocking_set_info[abs(lit)].neg_depends;
    }

    
    bool encoding_variable_not_in_cluster;
    set<int> problem_variable_set;
    set<int> encoding_variable_set;
    set<int> clause_ids_set;
    set<int> new_clause_ids_set;
    vector<int> problem_variables;
    vector<int> encoding_variables;



};

}

#endif