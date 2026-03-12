#include "cnf2knf.hpp"
#include "eval.hpp"

namespace cnf2knf {

using namespace std;
using namespace trustbdd;

    // Simply turn all data variables into an AMO constrain by negating the literals
    //  Lower bound on cardinality constraint is size - 1
    Klause default_AMO (vector<int> data_variables) {
	vector<int> new_klause_literals;
	for (auto v : data_variables) new_klause_literals.push_back(-v);
	Klause klause(new_klause_literals, new_klause_literals.size()-1);
	return klause;
    }



    int Cnf_extractor::bdd_analyze (int nvar, int ndata, vector<vector<int>> &constraint_clauses, vector<int> & norm_ordering, unordered_map<int, int> & from_normalization) {
        // number of klauses generated (0, 1, or 2)
        int nKlauses = 0;
        vector<int> lits;
        int lower;
        int upper;
        unsigned seed = 123456;
        Ordering O(nvar, ndata, 1);

        // cout << "c Starting BDD analysis with " << constraint_clauses.size() << " clauses and " << nvar << " variables." << endl;
        for (auto literals : constraint_clauses) {
            int len = literals.size();
            int *data = literals.data();
            O.add_clause(data, len);
        }

        ilist ordering;

        // cout << "c Normalized clauses added to ordering object." << endl;

        if (norm_ordering.size() == 0) {
          int ord_type = 0;
          if (extractor_options["totalizer_extract"] == "true")
            ord_type = 1;
          // cout << "c Generating variable ordering for BDD analysis with type " << ord_type << endl;
          ordering = O.generate_ordering(seed, ord_type);

          string temp_s = "Generated Ordering: "; 
          for (int i = 0; i < nvar; i++) {
              norm_ordering.push_back(ordering[i]);
              temp_s += to_string(from_normalization[ordering[i]]) + " ";
          } 
          log_ex_comment (temp_s, 2);
        } else {
          ordering = O.generate_ilist (norm_ordering);
        }

        

        int vlevel = 0;
        TermSet T(nvar, ndata, ordering, vlevel);
        T.add_normalization(from_normalization);
        for (auto literals : constraint_clauses) {
            int len = literals.size();
            int *data = literals.data();
            T.add_clause(data, len);
        }
        if (!T.bucket_reduce()) {
            // cout << "c Bucket reduce failed" << endl;
            ilist_free(ordering);
            return 0;
        }
        ilist_free(ordering);
        if (!T.cardinality_converter(lits, &lower, &upper)) {
            // cout << "c No cardinality constraints found" << endl;
            return 0;
        }
        // cout << "c Lower " << lower << " Upper " << upper << endl;
        if (lower > 0 && lower != (int) lits.size()) {
            Klause klow = Klause(lits, lower);
            analyzed_klauses.push_back(klow);
            nKlauses++;
        }
        if (upper < ndata && upper != 0) {
            for (int i = 0; i < lits.size(); i++) 
            lits[i] = -lits[i];
            Klause khigh = Klause(lits, ndata-upper);
            analyzed_klauses.push_back(khigh);
                nKlauses++;
        }
        return nKlauses;
    }

}
