
#include "cnf2knf.hpp"


using namespace std;


namespace cnf2knf {

//*****************************************************************************
// Basic Veification Functions

bool SatSolver::random_testing_prefilter (int nSAT_simulations, int nUNSAT_simulations, float percent_tight_simulations) {

  this->nSAT_simulations = nSAT_simulations;
  this->nUNSAT_simulations = nUNSAT_simulations;
  this->percent_tight_simulations = percent_tight_simulations;

  // First find the bound and ALK orientation
  find_bound_by_simulation();

  if (bound <= 0 || bound >= data_vars.size() || (bound == 1 && ALK) || (bound == data_vars.size() - 1 && !ALK)) {
    cout << "c Trivial constraint bound " << bound << " with n variables " << data_vars.size () << "ALK " << ALK << endl;
    return false;
  }

  // Then, run simulations to verify
  int nFails = run_guided_simulation();

  return (nFails == 0);
}

bool SatSolver::verify_with_sat (bool match_tree, bool is_scnt) {

  find_bound_by_simulation();

  if (bound <= 0 || bound >= data_vars.size() || (bound == 1 && ALK) || (bound == data_vars.size() - 1 && !ALK)) {
    cout << "c Trivial constraint bound " << bound << " with n variables " << data_vars.size () << "ALK " << ALK << endl;
    return false;
  }

  // First build the new encoding
  vector<int> output_lits; 
  vector<vector<int>> encoded_clauses;
  if (is_scnt) {
    build_sequential_counter(data_vars, encoded_clauses, output_lits, nvars+1, data_vars.size() - 1);
  } else {

    if (match_tree) {
      totalizer_node *existing_node = build_existing_totalizer_tree(data_vars, original_clauses, nvars);
      if (existing_node == nullptr) {
        build_totalizer_encoding(data_vars, encoded_clauses, output_lits, nvars+1);
      } else {
        build_totalizer_encoding_from_existing_tree(data_vars, encoded_clauses, output_lits, nvars+1, existing_node);
      }
    } else {
      build_totalizer_encoding(data_vars, encoded_clauses, output_lits, nvars+1);
    }
  }

  // Now add the encoded clauses to a new solver
  CaDiCaL::Solver *new_solver;
  new_solver = new CaDiCaL::Solver();


  int var_max = 0;
  for (const auto &clause : encoded_clauses) {
    for (int lit : clause) {
      int var = abs(lit);
      if (var > var_max) {
        var_max = var;
      }
    }
  }
  
  add_clauses_directly(original_clauses, new_solver);
  add_clauses_directly(encoded_clauses, new_solver);

  // Now start the solving loop
  int res, verified = true;
  
  // check that both bounds are as expected (SAT for on bound)
  // SAT call
  if (ALK) {
      new_solver->assume(-output_lits[bound]);
    } else {
      new_solver->assume(output_lits[bound-1]);
    }
  res = new_solver->solve();
  // cout << "c k res " << res << " bound " << bound  << " ALK " << ALK << endl;
  if (res != 10)
    verified = false;

  if (verified) {
    // unsat check 
    if (ALK) {
      new_solver->assume(-output_lits[bound-1]);
    } else {
      new_solver->assume(output_lits[bound]);
    }
    res = new_solver->solve();
    // cout << "c k res " << res << " bound " << bound << endl;
    if (res != 20)
      verified = false;
  }

  new_solver->statistics();

  delete new_solver;

  return verified;
}

bool SatSolver::verify_with_BDD () {
  // handled directly in the extractor API
  return false;
}

//*****************************************************************************
// Helper Simulation Functions

void SatSolver::find_bound_by_simulation () {
  
  // Determine if ALK or AMK with quick SAT check setting all data variables to true
  for (int var : data_vars) {
    solver->assume(-var);
  }   
  int res = solver->solve();
  if (res == 20) {
    ALK = true;
  } else {
    ALK = false;
  }

  int expected_result = res;
  bound = 1;

  while (bound <= data_vars.size()) {
    // Add data variables as assumptions
    for (int i = 0; i < bound; i++) 
      solver->assume(data_vars[i]);
    for (int i = bound; i < data_vars.size(); i++) 
      solver->assume(-data_vars[i]);

    // check satisfiability
    res = solver->solve();
    if (res != expected_result) break;

    bound++;
  }

  // last call is unsat so we need to decrement the bound by one
  if (!ALK) bound--;

  cout << "c SIMULATION found bound " << bound << " with ALK " << ALK << endl;
  
}

void SatSolver::make_simulation_assumptions(int nTrue) {
  // Make assumption with a random nTrue literals from data_vars

  vector<int> data_vars_values;
  // set all to 0 initially
  data_vars_values.resize(data_vars.size(), -1);
  // set first nTrue variables to true
  for (int i = 0; i < nTrue; i++) {
    data_vars_values[i] = 1;
  }

  // shuffle the data_vars_values
  shuffle(data_vars_values.begin(), data_vars_values.end(), rng);

  // add the assumptions to the solver
  for (int i = 0; i < data_vars_values.size(); i++) {
    solver->assume(data_vars_values[i] * data_vars[i]);
  }

}

bool SatSolver::run_simulation(int nTrue, int expected_result) {

    make_simulation_assumptions(nTrue);

    // check satisfiability
    int res = solver->solve();

    return res == expected_result;
}

int SatSolver::run_guided_simulation () {
  int nSAT_success = 0, nSAT_fails = 0;
  int nUNSAT_success = 0, nUNSAT_fails = 0;
  int res;
  int n = data_vars.size();
  cout << "Bound: " << bound << " n vars: " << n << endl;

  for (int i = 0; i < nSAT_simulations; i++) {
    if (i <= nSAT_simulations * percent_tight_simulations) {
      (run_simulation(bound, 10)) ? nSAT_success++ : nSAT_fails++;
    } else {
      // Randomly choose a number of true literals
      int nTrue;
      if (ALK) { // choose between bound and nvars
        std::uniform_int_distribution<int> dist(bound, n);
        nTrue = dist(rng);
      } else { // choose between 0 and bound
        std::uniform_int_distribution<int> dist(0, bound);
        nTrue = dist(rng);
      }
      (run_simulation(nTrue, 10)) ? nSAT_success++ : nSAT_fails++;
    }
  }

  cout << "c SIM SAT simulations: " << nSAT_success << " success, " << nSAT_fails << " fails" << endl;

  for (int i = 0; i < nUNSAT_simulations; i++) {
    if (i <= nUNSAT_simulations * percent_tight_simulations) {
      int nTrue = ALK ? bound - 1 : bound + 1;
      (run_simulation(nTrue, 20)) ? nUNSAT_success++ : nUNSAT_fails++;
    } else {
      // Randomly choose a number of true literals
      int nTrue;
      if (!ALK) { // choose between bound and nvars
        std::uniform_int_distribution<int> dist(bound + 1, n);
        nTrue = dist(rng);
      } else { // choose between 0 and bound
        std::uniform_int_distribution<int> dist(0, bound - 1);
        nTrue = dist(rng);
      }
      (run_simulation(nTrue, 20)) ? nUNSAT_success++ : nUNSAT_fails++;
    }
  }

  cout << "c SIM UNSAT simulations: " << nUNSAT_success << " success, " << nUNSAT_fails << " fails" << endl;

  return nSAT_fails + nUNSAT_fails; // return the number of failed simulations
}

//*****************************************************************************
// Sequential Counter Encoding

void SatSolver::build_sequential_counter (vector<int> &data_vars, vector<vector<int>> &clauses, vector<int> &output_lits, int nvars, int bound) {
  // Build the sequential counter

  int n = data_vars.size();

  vector<vector<int>> var_matrix;
  for (int i = 0; i < n; i++) {
    vector<int> col(bound+2,-1);
    col[0] =(data_vars[i]); // First variable is the data variable
    var_matrix.push_back(col);
  }

  // encode the columns of the sequential counter
  for (int col = 0; col < n; col++) {
    int data_var = data_vars[col];

    int max_row = min (col+1, bound+1);

    for (int row = 0; row < max_row; row++) {
      int next_var = nvars++;
      var_matrix[col][row+1] = next_var; // Store the next variable in the matrix

      if (col == 0 && row == 0) {
        // s1,0 -> x1
        // x1 -> s1,0
        clauses.push_back({-next_var, data_var});
        clauses.push_back({next_var, -data_var});
      } else if (row == 0 && col > 0) {
        // s1,i -> (xi v s1,i-1)
        
        // xi -> s1,i
        // s1,i-1 -> s1,i

        int prev_col = var_matrix[col-1][row+1];
        // backwards
        clauses.push_back({-next_var, data_var, prev_col}); 
        // forwards
        clauses.push_back({next_var, -data_var});
        clauses.push_back({next_var, -prev_col});
      } else {
        int prev_col_down = var_matrix[col-1][row];
        if (col >= bound || row != col) {
          // Something behind

          // s_j,i -> (s_j,i-1 v s_j-1,i-1)
          // s_j,i -> (s_j,i-1 v xi)

          // s_j,i-1 -> s_j,i
          // xi ^ s_j-1,i-1 -> s_j,i

          int prev_col = var_matrix[col-1][row+1];
          // backwards
          clauses.push_back({-next_var, prev_col, prev_col_down});
          clauses.push_back({-next_var, prev_col, data_var});
          // forwards
          clauses.push_back({next_var, -prev_col});
          clauses.push_back({next_var, -prev_col_down, -data_var});
        } else {
          // Nothing behind

          // si,j -> si-1,j-1
          // si,j -> xi

          // xi ^ s_j-1,i-1 -> s_j,i

            //backwards
          clauses.push_back({-next_var, prev_col_down});
          clauses.push_back({-next_var, data_var});
          // forwards
          clauses.push_back({next_var, -prev_col_down, -data_var});
        
        }
      }
    }

    for (int row = 1; row < max_row; row++) {
      clauses.push_back({-var_matrix[col][row+1], var_matrix[col][row]});
    }

  }

  for (int i = 1; i <= bound + 1; i++) {
    output_lits.push_back(var_matrix[n-1][i]);
  }

}

// //*****************************************************************************
// // Totalizer Encoding

bool SatSolver::is_totalizer_leaf (totalizer_node * node) {
  // Check if the node is a leaf (no children)
  return node->left == nullptr && node->right == nullptr;
}

vector<int> SatSolver::totalizer_mid_variables(int left_size, int right_size, int bound, int &nvars) {
  // Generate mid variables for the totalizer node
  vector<int> mid_vars;

  int mid_size = min (left_size + right_size , bound + 1);
  for (int i = 0; i < mid_size; i++) {
    mid_vars.push_back(nvars++); // Use nvars as base for new variables
  }
  return mid_vars;
}

void SatSolver::add_totalizer_node_clauses(totalizer_node *node, int bound, vector<vector<int>> &clauses) {
  if (is_totalizer_leaf(node)) {
    // If it's a leaf, we don't need to add any clauses
    return;
  }
  
  vector<int> left_counters = node->left ? node->left->counters : vector<int>();
  vector<int> right_counters = node->right ? node->right->counters : vector<int>();
  vector<int> mid_counters = node->counters;

  if (left_counters.empty() || right_counters.empty()) {
    cout << "c Error: One of the children is empty, cannot add clauses." << endl;
    exit (1);
  }

  // Add clauses for the totalizer node

  // ALK clauses
  // forwards clauses

  // initial clauses
  for (unsigned i = 0; i < left_counters.size() && i < bound + 1 ; i++) 
    clauses.push_back ({mid_counters[i],-left_counters[i]});
  for (unsigned i = 0; i < right_counters.size() && i < bound + 1 ; i++) 
    clauses.push_back ({mid_counters[i],-right_counters[i]});

  // left[i] + right[j] = mid[i + j + 1]
  int sum;
  for (unsigned i = 0; i < left_counters.size(); i++) {
    for (unsigned j = 0; j < right_counters.size(); j++) {
      sum = i + j + 2;
      if (sum > bound + 1) continue;
      // printf("left %d, right  %d, sum %d\n", i, j,sum-1);
      clauses.push_back ({mid_counters[sum-1],-left_counters[i],-right_counters[j]});
    }
  }

  // AMK clauses
  // backwards clauses

  // initial clauses
  // 0 + 0 = 0; 1 + 1 >= 1
  clauses.push_back ({-mid_counters[0],left_counters[0], right_counters[0]});

  // 0 + n = n, 1 + n + 1 >= n + 1
  if (left_counters.size() > 0) {
    for (unsigned i = 1; i <= left_counters.size(); i++) {
      if (i >= bound)
        continue;
      if (i == left_counters.size())
        clauses.push_back({-mid_counters[i],right_counters[0]});
      else
        clauses.push_back({-mid_counters[i],left_counters[i], right_counters[0]});
    }
  }

  if (right_counters.size() > 0) {
    for (unsigned i = 1; i <= right_counters.size(); i++) {
      if (i >= bound)
        continue;
      if (i == right_counters.size())
        clauses.push_back({-mid_counters[i],left_counters[0]});
      else
        clauses.push_back({-mid_counters[i],right_counters[i], left_counters[0]});
    }
  }

  // left[i] + right[j] = mid[i + j + 1]
  for (unsigned i = 0; i < left_counters.size(); i++) {
    for (unsigned j = 0; j < right_counters.size(); j++) {
      sum = i + j + 2 + 1;
      if (sum > bound) continue;
      if (i+1 == left_counters.size() && j+1 == right_counters.size()) continue;
      if (i+1 == left_counters.size()) {
        clauses.push_back ({-mid_counters[sum-1],right_counters[j+1]});
      } else if (j+1 == right_counters.size()) {
        clauses.push_back ({-mid_counters[sum-1],left_counters[i+1]});
      } else {
        clauses.push_back ({-mid_counters[sum-1],left_counters[i+1],right_counters[j+1]});
      }
    }
  }
  
  // implication of sums
  for (unsigned i = 0; i < mid_counters.size(); i++) {
    // mid[i] implies mid[i-1]
    if (i > 0) {
      clauses.push_back({-mid_counters[i], mid_counters[i-1]});
    }
  }
}

void SatSolver::build_totalizer_encoding(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars) {
  // build the totalizer encoding for the cardinality constraint
  int n = data_vars.size();

  // First build the totalizer tree
  vector<totalizer_node*> unmatched_nodes;

  for (int i = 0; i < n; i++) {
    totalizer_node *node = new totalizer_node();
    node->counters.push_back(data_vars[i]);
    unmatched_nodes.push_back(node);
  }

  while (unmatched_nodes.size() > 1) {
    // Create a new layer of totalizer nodes
    // Each node combines two unmatched nodes from the previous layer
    // If there is an odd number of unmatched nodes, the last one is matched with the last matched node
    vector<totalizer_node*> next_layer;

    for (size_t i = 0; i < unmatched_nodes.size() / 2; i++) {
      totalizer_node *left = unmatched_nodes[2 * i];
      totalizer_node *right = unmatched_nodes[2 * i + 1];
      vector<int> mid_literals = totalizer_mid_variables(left->counters.size(), right->counters.size(), n - 1, nvars);
      totalizer_node * mid_node = new totalizer_node(mid_literals, left, right);
      next_layer.push_back(mid_node);
    }

    // Handle odd node
    if (unmatched_nodes.size() % 2 == 1) {
      totalizer_node *last_node = unmatched_nodes.back();
      totalizer_node *last_matched_node = next_layer.back();
      next_layer.pop_back();
      vector<int> mid_literals = totalizer_mid_variables(last_node->counters.size(), last_matched_node->counters.size(), n - 1, nvars);
      totalizer_node *mid_node = new totalizer_node(mid_literals, last_node, last_matched_node);
      next_layer.push_back(mid_node);
    }

    unmatched_nodes = next_layer;
  }

  totalizer_node *root = unmatched_nodes[0];
  output_lits.clear();
  output_lits = root->counters;

  // Now traverse the totalizer tree and generate clauses
  vector<totalizer_node*> nodes_to_add_clauses;
  nodes_to_add_clauses.push_back(root);
  while (!nodes_to_add_clauses.empty()) {
    totalizer_node *current_node = nodes_to_add_clauses.back();
    nodes_to_add_clauses.pop_back();
    
    // Add clauses for the current node
    add_totalizer_node_clauses(current_node, n - 1, new_clauses);
    
    // Add children to the stack
    if (current_node->left) {
      nodes_to_add_clauses.push_back(current_node->left);
    }
    if (current_node->right) {
      nodes_to_add_clauses.push_back(current_node->right);
    }
    
  }
  
  delete root; // Clean up the root node
}

totalizer_node * SatSolver::traverse_existing_tree (totalizer_node* current_node, int &nvars, vector<bool> &used_vars, int ndata_vars, unordered_map<int, int> &data_vars_polarity_map) {

  if (is_totalizer_leaf(current_node)) {
    // make new node for data variable
    totalizer_node *new_node = new totalizer_node();
    
    for (int lit : current_node->counters) {
      int var = abs(lit);
      if (used_vars[var]) {
        cout << "c Error: Variable " << var << " is already used." << endl;
        exit(1);
      }
      used_vars[var] = true;
      new_node->counters.push_back(var * data_vars_polarity_map[lit]);
    }
    return new_node;
  } 

  // else we do the traversal
  totalizer_node *left = traverse_existing_tree(current_node->left, nvars, used_vars, ndata_vars, data_vars_polarity_map);
  totalizer_node *right = traverse_existing_tree(current_node->right, nvars, used_vars, ndata_vars, data_vars_polarity_map);
  vector<int> mid_literals = totalizer_mid_variables(left->counters.size(), right->counters.size(), ndata_vars - 1, nvars);
  totalizer_node *new_node = new totalizer_node(mid_literals, left, right);
  return new_node;
}

void SatSolver::build_totalizer_encoding_from_existing_tree(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars, totalizer_node * existing_tree) {
  // build the totalizer encoding for the cardinality constraint

  int n = data_vars.size();
  vector<bool> used_vars(nvars + 1, false);

  unordered_map<int, int> data_vars_polarity_map;
  for (auto &var : data_vars) {
    if (var > 0) {
      data_vars_polarity_map[var] = 1; // positive polarity
    } else {
      data_vars_polarity_map[-var] = -1; // negative polarity
    }
  }

  totalizer_node *root = traverse_existing_tree(existing_tree, nvars, used_vars, n, data_vars_polarity_map);
  
  // check all data variables and only data variables are used
  for (int i = 0; i < used_vars.size(); i++) {
    if (used_vars[i] && (find(data_vars.begin(), data_vars.end(), i) == data_vars.end() && find(data_vars.begin(), data_vars.end(), -i) == data_vars.end())) {
      cout << "c Error: Variable " << i << " is used but not in data variables." << endl;
      exit(1);
    }
    if (!used_vars[i] && (find(data_vars.begin(), data_vars.end(), i) != data_vars.end() || find(data_vars.begin(), data_vars.end(), -i) != data_vars.end())) {
      cout << "c Error: Variable " << i << " is in data variables but not used." << endl;
      exit(1);
    }
  }

  output_lits.clear();
  output_lits = root->counters;

  // Now traverse the totalizer tree and generate clauses
  vector<totalizer_node*> nodes_to_add_clauses;
  nodes_to_add_clauses.push_back(root);
  while (!nodes_to_add_clauses.empty()) {
    totalizer_node *current_node = nodes_to_add_clauses.back();
    nodes_to_add_clauses.pop_back();
    
    // Add clauses for the current node
    add_totalizer_node_clauses(current_node, n - 1, new_clauses);

    // Add children to the stack
    if (current_node->left != nullptr) {
      nodes_to_add_clauses.push_back(current_node->left);
    }
    if (current_node->right != nullptr) {
      nodes_to_add_clauses.push_back(current_node->right);
    }

  }

  // Clean up the existing tree by deleting all nodes and children nodes
  delete existing_tree;
  delete root;

}

// // May have infinite loop if the totalizer tree is not well-formed
totalizer_node* SatSolver::build_existing_totalizer_tree(vector<int> data_vars, vector<vector<int>> &clauses, int nvars) {
  // First build a lookup map from variables to clause
  vector<vector<int>> var2_clause (nvars + 1);
  for (size_t clause_idx = 0; clause_idx < clauses.size(); clause_idx++) {
    const auto &clause = clauses[clause_idx];
    for (int lit : clause) {
      int var = abs(lit);
      var2_clause[var].push_back(clause_idx);
    }
  }

  unordered_map<int, totalizer_node*> var2_node;

  // Now build the totalizer tree from the data variables upwards
  vector<totalizer_node*> unmatched_nodes;
  for (int i = 0; i < data_vars.size(); i++) {
    totalizer_node *node = new totalizer_node();
    node->counters.push_back(abs(data_vars[i]));
    var2_node[abs(data_vars[i])] = node;
    unmatched_nodes.push_back(node);
  }

  // square root data_vars.size()
  int limit = data_vars.size() * (3 + sqrt(data_vars.size()));
  int cnt = 0;

  vector<bool> matched_vars(nvars + 1, false);
  while (unmatched_nodes.size() > 1) {
    if (cnt++ > limit) {
      for (auto node : unmatched_nodes) {
        delete node;
      }
      return nullptr;
    }

    totalizer_node *head = unmatched_nodes[0];

    // look for a match
    vector<totalizer_node*> matched_nodes;
    vector<int> new_counters;
    for (int head_counter : head->counters) {
      for (int clause_idx : var2_clause[head_counter]) {
        for (int lit : clauses[clause_idx]) {
          int var = abs(lit);
          if (matched_vars[var]) continue; // Skip already matched variables
          if (var2_node.find(var) != var2_node.end()) {
            matched_nodes.push_back(var2_node[var]);
          } else {
            new_counters.push_back(var);
          }
        }
      }
    }

    // Remove duplicates from new_counters
    sort(new_counters.begin(), new_counters.end());
    new_counters.erase(unique(new_counters.begin(), new_counters.end()), new_counters.end());

    // Remove duplicates from matched_nodes
    sort(matched_nodes.begin(), matched_nodes.end(), [](totalizer_node* a, totalizer_node* b) {
      return a->counters < b->counters;
    }); 
    matched_nodes.erase(unique(matched_nodes.begin(), matched_nodes.end()), matched_nodes.end());

    // remove head from matched_nodes
    matched_nodes.erase(remove(matched_nodes.begin(), matched_nodes.end(), head), matched_nodes.end());

    if (matched_nodes.size() > 1) {
      cout << "c Warning: More than one match found for node with counters: " << endl;


      // Not ready for merge, add head back to end of the list
      unmatched_nodes.push_back(head);
      unmatched_nodes.erase(unmatched_nodes.begin());
      continue;
    }

    if (matched_nodes.empty()) {
      // cout << "c No match found for node with counters: " << endl;

      // No match found, add head back to end of the list
      unmatched_nodes.push_back(head);
      unmatched_nodes.erase(unmatched_nodes.begin());
      continue;
    }

    // Merge matched nodes
    
    // cout << "c Merging nodes with counters: ";
    for (const auto &counter : head->counters) {
      // cout << counter << " ";
      matched_vars[counter] = true;
    }
    // cout << "and ";
    for (const auto &node : matched_nodes) {
      for (const auto &counter : node->counters) {
        // cout << counter << " ";
        matched_vars[counter] = true;
      }
    }
    // cout << endl;
    // // cout << "c New counters: ";
    // for (const auto &counter : new_counters) {
    //   cout << counter << " ";
    // }
    // cout << endl;

    totalizer_node *new_node = new totalizer_node(new_counters, head, matched_nodes[0]);

    for (const auto &counter : new_counters) {
      var2_node[counter] = new_node;
    }

    // Remove head from list
    unmatched_nodes.erase(unmatched_nodes.begin());
    // Remove matched node from list
    unmatched_nodes.erase(remove(unmatched_nodes.begin(), unmatched_nodes.end(), matched_nodes[0]), unmatched_nodes.end());
    unmatched_nodes.push_back(new_node);

  }

  return unmatched_nodes[0]; // Return the root of the totalizer tree

}

}