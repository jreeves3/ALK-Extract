#include "../src/cadical.hpp"

#include <iostream>
#include <fstream>
#include <chrono>
#include <cstdlib> 
#include <unordered_map>
#include <vector>
#include <algorithm>
#include <random>

// Must be placed in cadical directory so that 
// the include statement in line 1 works.
// This will also ensure that the makefile
// compiles the code correctly.


using namespace std;


void build_sequential_counter (vector<int> &data_vars, vector<vector<int>> &clauses, vector<int> &output_lits, int nvars, int bound) {
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

    // if (col + 1 > bound) {
    //   int next_var = nvars++;
    //   var_matrix[col][bound+1] = next_var; // Store the next variable in the matrix

    //   int prev_col_down = var_matrix[col-1][bound];
    //   clauses.push_back({next_var, -prev_col_down, -data_var});
    // }
  }

  for (int i = 1; i <= bound + 1; i++) {
    output_lits.push_back(var_matrix[n-1][i]);
  }

}

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

bool is_totalizer_leaf (totalizer_node * node) {
  // Check if the node is a leaf (no children)
  return node->left == nullptr && node->right == nullptr;
}

vector<int> totalizer_mid_variables(int left_size, int right_size, int bound, int &nvars) {
  // Generate mid variables for the totalizer node
  vector<int> mid_vars;

  int mid_size = min (left_size + right_size , bound + 1);
  for (int i = 0; i < mid_size; i++) {
    mid_vars.push_back(nvars++); // Use nvars as base for new variables
  }
  return mid_vars;
}

void add_totalizer_node_clauses(totalizer_node *node, int bound, vector<vector<int>> &clauses) {
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

void build_totalizer_encoding(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars) {
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

totalizer_node * traverse_existing_tree (totalizer_node* current_node, int &nvars, vector<bool> &used_vars, int nDataVars, unordered_map<int, int> &data_vars_polarity_map) {

  // cout << "c Traversing existing tree with left and right children." << current_node->left->counters[0] << endl;

  // cout << "node with counters: ";
  // for (const auto &counter : current_node->counters) {
  //   cout << counter << " ";
  // }
  // cout << endl;

  if (is_totalizer_leaf(current_node)) {
    // make new node for data variable
    // cout << "is leaf" << endl;
    totalizer_node *new_node = new totalizer_node();
    
    for (int lit : current_node->counters) {
      int var = abs(lit);
      cout << "c Adding variable " << var << " to totalizer node." << endl;
      if (used_vars[var]) {
        cout << "c Error: Variable " << var << " is already used." << endl;
        exit(1);
      }
      used_vars[var] = true;
      new_node->counters.push_back(var * data_vars_polarity_map[lit]);
    }
    return new_node;
  } //else cout << "Not leaf" << endl;

  // cout << "c Traversing existing tree with left and right children." << current_node->left->counters[0] << endl;

  // else we do the traversal
  totalizer_node *left = traverse_existing_tree(current_node->left, nvars, used_vars, nDataVars, data_vars_polarity_map);
  totalizer_node *right = traverse_existing_tree(current_node->right, nvars, used_vars, nDataVars, data_vars_polarity_map);
  vector<int> mid_literals = totalizer_mid_variables(left->counters.size(), right->counters.size(), nDataVars - 1, nvars);
  totalizer_node *new_node = new totalizer_node(mid_literals, left, right);
  return new_node;
}

void build_totalizer_encoding_from_existing_tree(vector<int> data_vars, vector<vector<int>> & new_clauses, vector<int> & output_lits, int nvars, totalizer_node * existing_tree) {
  // build the totalizer encoding for the cardinality constraint

  cout << "entering" << endl;
  int n = data_vars.size();
  vector<bool> used_vars(nvars + 1, false);
  cout << "c Building totalizer encoding from existing tree with " << n << " data variables." << endl;

  unordered_map<int, int> data_vars_polarity_map;
  for (auto &var : data_vars) {
    if (var > 0) {
      data_vars_polarity_map[var] = 1; // positive polarity
    } else {
      data_vars_polarity_map[-var] = -1; // negative polarity
    }
  }

  // cout << existing_tree->left->counters[0] << endl;

  totalizer_node *root = traverse_existing_tree(existing_tree, nvars, used_vars, n, data_vars_polarity_map);
  
  cout << "c Totalizer encoding generated with " << root->counters.size() << " output literals." << endl;

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

  cout << "c All data variables are used correctly." << endl;
  
  output_lits.clear();
  output_lits = root->counters;

  // Now traverse the totalizer tree and generate clauses
  vector<totalizer_node*> nodes_to_add_clauses;
  nodes_to_add_clauses.push_back(root);
  while (!nodes_to_add_clauses.empty()) {
    totalizer_node *current_node = nodes_to_add_clauses.back();
    nodes_to_add_clauses.pop_back();

    cout << "c Adding clauses for node with counters: ";
    for (auto counter : current_node->counters) {
      cout << counter << " ";
    }
    cout << endl;
    
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

totalizer_node* build_existing_totalizer_tree(vector<int> data_vars, vector<vector<int>> &clauses, int nvars) {
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

  vector<bool> matched_vars(nvars + 1, false);
  while (unmatched_nodes.size() > 1) {
    totalizer_node *head = unmatched_nodes[0];

    cout << "c Processing node with counters: ";
    for (const auto &counter : head->counters) {
      cout << counter << " ";
    }
    cout << endl;

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
      cout << "c No match found for node with counters: " << endl;

      // No match found, add head back to end of the list
      unmatched_nodes.push_back(head);
      unmatched_nodes.erase(unmatched_nodes.begin());
      continue;
    }

    // Merge matched nodes
    
    cout << "c Merging nodes with counters: ";
    for (const auto &counter : head->counters) {
      cout << counter << " ";
      matched_vars[counter] = true;
    }
    cout << "and ";
    for (const auto &node : matched_nodes) {
      for (const auto &counter : node->counters) {
        cout << counter << " ";
        matched_vars[counter] = true;
      }
    }
    cout << endl;
    cout << "c New counters: ";
    for (const auto &counter : new_counters) {
      cout << counter << " ";
    }
    cout << endl;

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

// *****************************************************************************
// Guided Random Simulation

int find_bound_by_simulation (vector<int> data_vars, vector<vector<int>> &clauses, int nvars, int min_bound, int max_bound, bool ALK) {
  // This function will simulate the solving process and find the bound
  // for the encoding by checking the satisfiability of the clauses
  // with increasing bounds.

  CaDiCaL::Solver *solver = new CaDiCaL::Solver;

  // load the clauses
  for (const auto &clause : clauses) {
    for (int lit : clause) {
      solver->add(lit);
    }
    solver->add(0); // end of clause
  }

  int res = ALK ? 20 : 10; // UNSAT for ALK, SAT for AMK
  int expected_result = res;

  while (min_bound <= max_bound) {
    cout << "c Trying bound: " << min_bound << endl;

    // Add data variables as assumptions
    for (int i = 0; i < min_bound; i++) {
      solver->assume(data_vars[i]);
    }
    for (int i = min_bound; i < data_vars.size(); i++) {
      solver->assume(-data_vars[i]);
    }

    // check satisfiability
    res = solver->solve();

    cout << "c Result for bound " << min_bound << ": " << res << endl;

    if (res != expected_result) break;

    min_bound++;
  }

  if (!ALK) min_bound--; // If ALK, we want the last bound that was UNSAT, so we don't decrement

  delete solver;

  return min_bound;
}

void make_simulation_assumptions(CaDiCaL::Solver *solver, vector<int> &data_vars, int nTrue, bool ALK, std::default_random_engine &rng) {
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

bool run_simulation(CaDiCaL::Solver *solver, vector<int> &data_vars, int nTrue, bool ALK, default_random_engine &rd, int expected_result) {

    make_simulation_assumptions(solver, data_vars, nTrue, ALK, rd);

    // check satisfiability
    int res = solver->solve();

    return res == expected_result;
}

int guided_simulation(vector<int> data_vars, vector<vector<int>> &clauses, int bound, bool ALK, int nSAT_simulations, int nUNSAT_simulations, float percent_tight_simulations, unsigned int random_seed) {

  CaDiCaL::Solver *solver = new CaDiCaL::Solver;

  auto rng = std::default_random_engine {random_seed};
  int nvars = data_vars.size();

  // load the clauses
  for (const auto &clause : clauses) {
    for (int lit : clause) {
      solver->add(lit);
    }
    solver->add(0); // end of clause
  }

  int nSAT_success = 0, nSAT_fails = 0;
  int nUNSAT_success = 0, nUNSAT_fails = 0;
  int res;

  for (int i = 0; i < nSAT_simulations; i++) {
    if (i <= nSAT_simulations * percent_tight_simulations) {
      if (run_simulation(solver, data_vars, bound, ALK, rng, 10))
        nSAT_success++;
      else
        nSAT_fails++;
    } else {
      // Randomly choose a number of true literals
      int nTrue;
      if (ALK) { // choose between bound and nvars
        std::uniform_int_distribution<int> dist(bound, nvars);
        nTrue = dist(rng);
      } else { // choose between 0 and bound
        std::uniform_int_distribution<int> dist(0, bound);
        nTrue = dist(rng);
      }
      if (run_simulation(solver, data_vars, nTrue, ALK, rng, 10)) {
        nSAT_success++;
      } else {
        nSAT_fails++;
      }
    }
  }

  cout << "c SAT simulations: " << nSAT_success << " success, " << nSAT_fails << " fails" << endl;

  for (int i = 0; i < nUNSAT_simulations; i++) {
    if (i <= nUNSAT_simulations * percent_tight_simulations) {
      int nTrue = ALK ? bound - 1 : bound + 1;
      if (run_simulation(solver, data_vars, nTrue, ALK, rng, 20))
        nUNSAT_success++;
      else
        nUNSAT_fails++;
    } else {
      // Randomly choose a number of true literals
      int nTrue;
      if (!ALK) { // choose between bound and nvars
        std::uniform_int_distribution<int> dist(bound + 1, nvars);
        nTrue = dist(rng);
      } else { // choose between 0 and bound
        std::uniform_int_distribution<int> dist(0, bound - 1);
        nTrue = dist(rng);
      }
      if (run_simulation(solver, data_vars, nTrue, ALK, rng, 20)) {
        nUNSAT_success++;
      } else {
        nUNSAT_fails++;
      }
    }
  }

  cout << "c UNSAT simulations: " << nUNSAT_success << " success, " << nUNSAT_fails << " fails" << endl;

  delete solver;

  return nSAT_fails + nUNSAT_fails; // return the number of failed simulations

}


int main (int argc, char *argv[]) {

  // Start the timing
  auto start = std::chrono::high_resolution_clock::now();


  // ------------------------------------------------------------------
  // Read inputs

  // Usage <CNF file> [--bound=<bound>] [--ALK=<True/False>]

  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <CNF file> [--bound=<bound>] [--flip=<True/False>] [--sat=<True/False>] [--run_simulation=<True/False>] [--run_sat=<True/False>] [--simul_sat=<int>] [--simul_unsat=<int>] --[simul_percent_tight=<float>]" << std::endl;
    return 1;
  }

  string inputfile = argv[1];
  int bound = -1;
  bool flip = false;
  bool sat = false;
  bool run_simulation = false;
  bool run_sat = false;
  int nSAT_simulations = 100;
  int nUNSAT_simulations = 100;
  float percent_tight_simulations = 0.5;
  bool ALK = false;
  unsigned int random_seed = 0; // Seed for random number generator
  bool match_tree = false; // If true, we will use the existing totalizer tree from the input file
  bool is_scnt = false;

  if (argc > 2) {
    for (int i = 2; i < argc; i++) {
      string arg = argv[i];
      if (arg == "--flip=True" || arg == "--flip=1" || arg == "--flip")
        flip = true;
      else if (arg == "--sat=True" || arg == "--sat=1" || arg == "--sat")
        sat = true;
      else if (arg.find("--bound") == 0)
        bound = stoi(arg.substr(arg.find('=') + 1));
      else if (arg == "--run_simulation=True" || arg == "--run_simulation=1" || arg == "--run_simulation")
        run_simulation = true;
      else if (arg == "--run_sat=True" || arg == "--run_sat=1" || arg == "--run_sat")
        run_sat = true;
      else if (arg.find("--simul_sat") == 0) {
        nSAT_simulations = stoi(arg.substr(arg.find('=') + 1));
      } else if (arg.find("--simul_unsat") == 0) {
        nUNSAT_simulations = stoi(arg.substr(arg.find('=') + 1));
      } else if (arg.find("--simul_percent_tight") == 0) {
        percent_tight_simulations = stof(arg.substr(arg.find('=') + 1));
      } else if (arg.find("--ALK") == 0 || arg.find("--alk") == 0 || arg.find("--ALK=True") == 0) {
        ALK = true;
      } else if (arg.find("--random_seed") == 0) {
        random_seed = stoi(arg.substr(arg.find('=') + 1));
      } else if (arg == "--match_tree=True" || arg == "--match_tree=1" || arg == "--match_tree")
        match_tree = true;
      else if (arg == "--is_scnt=True" || arg == "--is_scnt=1" || arg == "--is_scnt")
        is_scnt = true;
      else {
        cerr << "e Error: Unknown argument " << arg << endl;
        return 1;
      }
    }
  }

  CaDiCaL::Solver *solver = new CaDiCaL::Solver;

  // ------------------------------------------------------------------
  // Read CNF from file

  // optional line s for data vars
  vector<int> dataVarsList;
  bool dataVarsListSet = false;

  ifstream infile(inputfile);
  if (!infile) {
    cerr << "e Error: Could not open file " << inputfile << endl;
    return 1;
  }
  int lit;
  int nvars = 0;
  int nclauses = 0;
  string s;
  
  infile >> s;
  // parse header
  do {
    if (s == "c") { // parse a comment line
      getline(infile, s);
      continue;
    }
    if (s == "p") { // parse the headr "p cnf <nvars> <nclauses>"
      infile >> s;
      if (s != "cnf" && s != "knf") {
        cerr << "Error: Invalid CNF file format" << endl;
        return 1;
      }
      infile >> nvars >> nclauses;
      break;
    }
    if (s == "s") {
      // parse list of data vars "s <dataVars> 0"
      while (infile >> s) {
        if (s == "0") {
          break;
        }
        dataVarsList.push_back((stoi(s)));
      }
      dataVarsListSet = true;
      continue;
    }
  } while (infile >> s);

  if (nvars <= 0) {
    cerr << "e Error: Invalid number of variables" << endl;
    return 1;
  }

  cout << "c Number of variables: " << nvars << endl;
  cout << "c Number of clauses: " << nclauses << endl;

  // Parse the clauses
  vector<vector<int>> original_clauses;
  vector<int> clause;
  bool isCardinality = false;
  int card_bound = 0;
  while (infile >> s) {
    if (s == "c") { // parse a comment line
      getline(infile, s);
      continue;
    }
    if (s == "s") {
      // parse list of data vars "s <dataVars> 0"
      while (infile >> s) {
        if (s == "0") {
          break;
        }
        dataVarsList.push_back((stoi(s)));
      }
      dataVarsListSet = true;
      continue;
    }
    // if (s == "k") { // parse a cardinality constraint
    //   isCardinality = true;
    //   infile >> card_bound;
    //   solver->CARadd(card_bound); // add the cardinality bound
    //   continue;
    // }
    lit = stoi(s); // parse a literal; '0' for end of a clause
    // if (isCardinality)
    //   solver->CARadd(lit); // add the literal to the cardinality constraint
    // else
      solver->add(lit); // add the literal to the clause

    if (lit == 0) {
      isCardinality = false;
    }

    if (lit != 0) {
      clause.push_back(lit);
    } else {
      if (!clause.empty()) {
        original_clauses.push_back(clause);
        clause.clear();
      }
    }
  }

  if (!dataVarsListSet) {
    cerr << "e Error: data vars not included in input CNF with 's' <datavars> 0 line" << endl;
    return 1;
  }

  // negate literals in dataVarsList
  if (flip) {
    for (auto &var : dataVarsList) {
      var = -var; // negate the literals
    }
  }

  cout << "c Data variables with " << (flip ? "" : "no ") << "flip: ";
  for (const auto &var : dataVarsList) {
    cout << var << " ";
  }
  cout << endl; 

  cout << "c Parsed " << original_clauses.size() << " clauses" << endl;




  if (run_sat) {

    // -------------------------------------------------------------------
    // Create totalizer encoding for the cardinality constraint.
    // Output units will be incrementally added to the solver.
    
    vector<vector<int>> new_clauses;
    vector<int> output_lits;

    if (is_scnt) {
      cout << "c Using SCNT encoding." << endl;
    
      build_sequential_counter(dataVarsList, new_clauses, output_lits, nvars+1, dataVarsList.size() - 1);
    
    } else {

      if (match_tree){
        cout << "c Matching existing totalizer tree from input clauses." << endl;
      
      totalizer_node *existing_node = build_existing_totalizer_tree(dataVarsList, original_clauses, nvars);

      build_totalizer_encoding_from_existing_tree(dataVarsList, new_clauses, output_lits, nvars+1, existing_node);
      } else {
        cout << "c Building totalizer encoding from scratch." << endl;
        build_totalizer_encoding(dataVarsList, new_clauses, output_lits, nvars+1);
      }
      cout << "c Totalizer encoding generated with " << output_lits.size() << " output literals." << endl;

    }

    cout << "c New clauses generated: " << new_clauses.size() << endl;
    cout << "c Output literals: ";
    for (const auto &lit : output_lits) {
      cout << lit << " ";
    }
    cout << endl;

    // Add the new clauses to the solver
    for (const auto &clause : new_clauses) {
      for (int lit : clause) {
        solver->add(lit);
        // cout << lit << " ";
      }
      // cout << "0" << endl;
      solver->add(0); // end of clause
    }

    // Cases for the solving process
    // For now, assuming input is the data variables for an ALK encoding

    // Decide direction to go through the unit clauses
    bool forwards = true;
    int outputs_sign = 1;
    int expected_result = 20; // UNSAT

    if (sat) {
      expected_result = 10; // SAT
      if (flip) {
        cout << "c Flipped the output literals for SAT solving." << endl;
        cout << "c Using ALK 0 ... bound - k - 1" << endl;
        forwards = true;
      } else {
        cout << "c Using AMK n ... k - 1" << endl;
        forwards = false; // go backwards
        outputs_sign = -1; // flip the output literals for AMK
      }
    } else {
      expected_result = 20; // UNSAT
      if (flip) {
        cout << "c Flipped the output literals for UNSAT solving." << endl;
        cout << "c Using ALK n ... bound - k - 1" << endl;
        forwards = false; // go backwards
      } else {
        cout << "c Using AMK 0 ... k - 1" << endl;
        forwards = true; // go forwards
        outputs_sign = -1; // flip the output literals for AMK
      }
    }

    if (bound == -1)
      bound = forwards ? 0 : output_lits.size() - 1;
    else {
      if (flip) bound = output_lits.size() - bound;
      if (sat) bound = output_lits.size() - bound;
      if (forwards) bound--;
    }

    // ------------------------------------------------------------------
    // Start the solving process
    // first call should be SAT
    auto start_solve = std::chrono::high_resolution_clock::now();
    int res = solver->solve (); // Solve instance.
    auto end_solve = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> solve_duration = end_solve - start_solve;
    cout << "c Initial solve result: " << res << " Solve time: " << solve_duration.count() << " seconds" << endl;

    res = expected_result;
    int prev_bound = bound;

    while (expected_result == res) {
      // add next output literal updating the bound
      if (forwards) {
        if (bound < output_lits.size() - 1) {
          solver->assume(outputs_sign * output_lits[bound++]);
          // solver->add(0); // end of clause
          cout << "c Added unit clause: " << outputs_sign * output_lits[prev_bound] << endl;
        } else {
          cout << "c No more unit clauses to add" << endl;
          break;
        }
      } else {
        if (bound > 0) {
          solver->assume(outputs_sign * output_lits[bound--]);
          // solver->add(0); // end of clause
          cout << "c Added unit clause: " << outputs_sign * output_lits[prev_bound] << endl;
        } else {
          cout << "c No more unit clauses to add" << endl;
          break;
        }
      }
      
      // Start the timing
      start_solve = std::chrono::high_resolution_clock::now();
      res = solver->solve (); // Solve instance.
      end_solve = std::chrono::high_resolution_clock::now();
      solve_duration = end_solve - start_solve;

      cout << "c Result: " << res << " Bound: " << prev_bound << " Solve time: " << solve_duration.count() << " seconds" << endl;
      prev_bound = bound;
    }
    

    delete solver;
  } else if (run_simulation) {

    // optionally get bound

    if (bound == -1) {
      cout << "c No bound specified, running guided simulation to find bound." << endl;
      bound = find_bound_by_simulation(dataVarsList, original_clauses, nvars, 0, dataVarsList.size() - 1, ALK);
      cout << "c Found bound: " << bound << endl;
    } else {
      cout << "c Using specified bound: " << bound << endl;
    }

    cout << "c Running guided simulation with bound: " << bound << endl;
    int nFailed = guided_simulation(dataVarsList, original_clauses, bound, ALK, nSAT_simulations, nUNSAT_simulations, percent_tight_simulations, random_seed);

    cout << "c Guided simulation finished with " << nFailed << " failed simulations." << endl;

  }

  // End the timing
  auto end = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> duration = end - start;
  cout << "c Time taken: " << duration.count() << " seconds" << endl;


  return 0;
}
