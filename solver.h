#include <vector>
#include <deque>
#include <unordered_map>

extern std::unordered_map<int, std::string> original_variable_names;
extern std::unordered_map<std::string, int> internal_variable_names;
extern std::unordered_map<std::string, int> original_prefix_position;
extern std::deque<int> internal_variable_original_quantifiers;
extern int variables;
extern int innermost_universal;
extern bool withQuantifierRearrange;

struct clause
{
  unsigned id;		// For debugging and sorting.
  unsigned size;
  unsigned glue;
  bool garbage;		// Marked as garbage clause.
  bool reason;		// Active reason clause.
  bool redundant;	// Learned redundant clause.
  bool used;		// Used since last reduction.
  int literals[];

  // The following two functions allow simple ranged-based for-loop
  // iteration over clause literals with the following idiom:
  //
  //   clause * c = ...
  //   for (auto lit : *c)
  //     do_something_with (lit);
  //
  int * begin () { return literals; }
  int * end () { return literals + size; }
};

int solve(void);
void initialize (void);
void universal_existential_reduction(std::vector<int>& literals, bool is_clause); 
clause * add_clause (bool redundant, unsigned glue, std::vector<int>& literals, bool is_clause);