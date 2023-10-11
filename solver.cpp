const char * usage =
"usage: simpleQCDCL [ <option> ... ] [ <qdimacs> | <qcir> ]\n"
"\n"
"where '<option>' can be one of the following\n"
"\n"
"  -h | --help        print this command line option summary\n"
#ifdef LOGGING
"  -l | --logging     print very verbose logging information\n"
#endif
"  -n | --no-witness  do not print witness if satisfiable\n"
" --qcir              for QCIR-Input files"
" -r                  for rearranging the quanitfier within QCIR-Inputs"
"\n"
"and '<qcir>' is th input file in QCIR format,\n '<qdimacs>' is the input file in QDIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n"
;

#include <cassert>
#include <climits>
#include <cstdarg>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <algorithm>
#include <string>

#include "solver.h"
#include "QCIRParser.h"

static unsigned reduce_interval = 1000;
static unsigned restart_interval = 50;
static double reduce_fraction = 0.75;

struct watch
{
  bool binary;
  int blocking;
  struct clause * clause;
  watch (bool bin = false, int literal = 0, struct clause * c = 0) :
    binary (bin), blocking (literal), clause (c) { }
};

struct link
{
  size_t stamp;
  link * prev, * next;
};

static struct 
{
  link * first, * last;
} queue;

static std::vector<clause*> clauses;
static std::vector<watch> * watches[2];
static std::vector<int> * deps;
static std::vector<int> * deps_watching;
static clause * empty[2];
static clause * initial_term;

static signed char * values;

static bool * seen;               // Variables marked flag for search.
static unsigned * levels;         // Mapping variables to decision level.
static clause ** reasons;         // Mapping variables to reason clauses.
static std::vector<int> learn;    // Literals added to learned clause.
static std::vector<int> analyzed; // Marked literals during search.

static std::vector<int> trail;
static std::vector<unsigned> control;
static std::vector<unsigned> level_occs; // During conflict analysis, track number of literals at each level.

static unsigned level;
static unsigned propagated;
static unsigned dependencies_propagated;

static size_t conflicts;
static size_t dependencies;
static size_t decisions;
static size_t propagations;

static int * minimizable;        // Variables marked as minimizable.
static std::vector<int> minimized;// Literals marked minimizable.

static link * links;
static link * search;

static size_t deduced;		// Literals before minimization.
static size_t learned;		// Learned literals after minimization.

static size_t added;		// Number of added clauses.
static size_t reductions;	// Number of clause-database reductions.
static size_t recycled;		// Number of recycled clauses.

static size_t stamp;
static size_t * stamps;

static size_t restarts;
static double slow_glue_average;
static double fast_glue_average;

static bool * phases;

static int fixed;

static struct 
{
  size_t reduce;
  size_t restart;
} next;

static std::unordered_map<unsigned int, bool> constraint_is_clause;

// Generates nice compiler warnings if format string does not fit arguments.

static void message (const char *, ...) __attribute__((format (printf, 1, 2)));
static void die (const char *, ...) __attribute__((format (printf, 1, 2)));

static void parse_error (const char * fmt, ...)
  __attribute__((format (printf, 1, 2)));

#ifdef LOGGING

static void debug (const char *, ...) __attribute__((format (printf, 1, 2))); 

static void debug (clause *, const char *, ...)
  __attribute__((format (printf, 2, 3)));

// Print debugging message if '--debug' is used.  This is only enabled
// if the solver is configured with './configure --logging' (which is the
// default for './configure --debug').  Even if logging code is included
// this way, it still needs to be enabled at run-time through '-l'.

static bool logging;

static char debug_buffer[4][32];
static size_t next_debug_buffer;

// Get a statically allocate string buffer (of size 32 bytes).
// Used here only for printing literals.

static char *
debug_string (void)
{
  char * res = debug_buffer[next_debug_buffer++];
  if (next_debug_buffer == sizeof debug_buffer / sizeof *debug_buffer)
    next_debug_buffer = 0;
  return res;
}

static const char *
original (int lit)
{
  auto var = abs(lit);
  auto og = original_variable_names[var];
  auto lit_str = lit > 0 ? og : "-" + og;
  return lit_str.c_str();
}

static char *
debug (int lit)
{
  if (!logging)
    return 0;
  char * res = debug_string ();
  sprintf (res, "%c%s", (abs(lit) % 2) ? 'e' : 'a', original(lit));
  int value = values[lit];
  if (value)
    sprintf (res + strlen (res), "@%u=%d", levels[abs (lit)], value);
  assert (strlen (res) <= sizeof debug_buffer[0]);
  return res;
}

static void
debug_prefix (void)
{
  printf ("c DEBUG %u ", level);
}

static void
debug_suffix (void)
{
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
debug (const char * fmt, ...)
{
  if (!logging)
    return;
  debug_prefix ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  debug_suffix ();
}

static void
debug (clause * c, const char *fmt, ...)
{
  if (!logging)
    return;
  debug_prefix ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c->redundant)
    printf (" redundant glue %u", c->glue);
  else
    printf (" irredundant");
  printf (" size %u ", c->size);
  printf ("constraint");
  printf ("[%u]", c->id);
  for (auto lit : *c)
    printf (" %s", debug (lit));
  debug_suffix ();
}

#else

#define debug(...) do { } while (0)

#endif

// Print message to '<stdout>' and flush it.

static void
message (const char * fmt, ...)
{
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

// Print error message and 'die'.

static void
die (const char * fmt, ...)
{
  fprintf (stderr, "solver: error: ");
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
enqueue (int idx, bool update)
{
  link * link = links + idx;
  if (queue.last)
    queue.last->next = link;
  else{
    queue.first = link;
    queue.first->prev = nullptr;
  }
  link->prev = queue.last;
  queue.last = link;
  link->next = 0;
  link->stamp = ++stamp;
  if (update || !search)
    search = link;
}

static void
dequeue (int idx)
{
  link * link = links + idx;
  if (link->next)
    link->next->prev = link->prev;
  else
    queue.last = link->prev;
  if (link->prev)
    link->prev->next = link->next;
  else
    queue.first = link->next;
}

static bool variable_is_existential(int var) {
  return var % 2;
}

 bool isOriginalVariable(int idx) {
  return std::find(internal_variable_original_quantifiers.begin(),internal_variable_original_quantifiers.end(),idx) 
                != internal_variable_original_quantifiers.end();
}

void
initialize (void)
{
  assert (variables < INT_MAX);
  unsigned size = variables + 1;

  unsigned twice = 2 * size;

  values = new signed char[twice];
  for (int i = 0; i <= 1; i++)
    watches[i] = new std::vector<watch>[twice];

  deps = new std::vector<int>[size];
  deps_watching = new std::vector<int>[size];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).

  for (int i = 0; i <= 1; i++)
    watches[i] += variables;
  values += variables;

  levels = new unsigned[size];
  seen = new bool[size];
  reasons = new clause*[size];

  for (int lit = -variables; lit <= variables; lit++)
    values[lit] = 0;

  for (int idx = 1; idx <= variables; idx++)
    seen[idx] = false, levels[idx] = 0, reasons[idx] = 0;

  minimizable = new int[size];

  for (int idx = 1; idx <= variables; idx++)
    minimizable[idx] = -1;

  stamps = new size_t[size];
  for (int level = 0; level <= variables; level++)
    stamps[level] = 0;

  links = new link[size];

  //Add all non prefix variables to queue 

  //TODO add line below so that only original prefixes are included into the queue
  if(!withQuantifierRearrange)
    for (int idx = variables; idx > 0; idx--)
      if (original_variable_names.find(idx) != original_variable_names.end() 
      && !isOriginalVariable(idx)) // Queue only contains "real" variables.
         enqueue (idx, false);

  //Add all prefixes to the end of queue
  for (int idx : internal_variable_original_quantifiers){
    enqueue (idx, false);
  }
  search = queue.last;

  phases = new bool[size];
  for (int idx = 1; idx <= variables; idx++)
    phases[idx] = false;

  assert (!propagated);
  assert (!level);
  assert (!dependencies_propagated);

  // Allocate memory for initial term.
  size_t nr_real_variables = (variables - 2) / 2;
  size_t bytes = sizeof (struct clause) + nr_real_variables * sizeof (int);
  initial_term = (clause*) new char [bytes];

  initial_term->id = 0;
  initial_term->size = 0;
  initial_term->redundant = true;
  initial_term->reason = false;
  initial_term->garbage = false;
  initial_term->used = true;
  initial_term->glue = 0;

  level_occs.push_back(0);
}

static clause pseudo_reason;
static clause * decision_reason = 0;
static clause * unit_reason = &pseudo_reason;

static void
delete_clause (clause * clause)
{
  assert (clause != decision_reason);
  assert (clause != unit_reason);
  debug (clause, "delete");
  delete [] clause;
}

static void
release (void)
{
  for (auto clause : clauses)
    delete_clause (clause);

  for (int i = 0; i <= 1; i++) {
    watches[i] -= variables;
    delete [] watches[i];
  }
  delete [] deps;
  delete [] deps_watching;

  values -= variables;
  delete [] values;

  delete [] levels;
  delete [] seen;
  delete [] reasons;

  delete [] minimizable;

  delete [] stamps;

  delete [] phases;
}

static void
assign (int lit, clause * reason)
{
  int idx = abs (lit);
  levels[idx] = level;
  fixed += !level;
  reasons[idx] = reason;
  phases[idx] = (lit < 0);
#ifdef LOGGING
  if (logging)
    {
      if (reason == decision_reason)
	debug ("assign %s as decision", debug (lit));
      else if (reason == unit_reason)
	debug ("assign %s as root-level unit", debug (lit));
      else
	debug (reason, "assign %s with reason", debug (lit));
    }
#endif
  assert (!values[lit]);
  assert (!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  trail.push_back (lit);
}

static void
watch_literal (int lit, struct clause * c, bool is_clause)
{
  bool binary = c->size == 2;
  int * literals = c->literals;
  int blocking = literals[literals[0] == lit];
  debug (c, "watching %s with blocking literal %s in %s",
         debug (lit), debug (blocking), is_clause ? "clause" : "term");
  struct watch watch (binary, blocking, c);
  watches[is_clause][lit].push_back (watch);
}

clause *
add_clause (bool redundant, unsigned glue, std::vector<int> & literals, bool is_clause)
{
#if 0
  // Uncomment to produce inlined DRAT proofs.

  if (redundant)
    {
      for (auto lit : literals)
	printf ("%d ", lit);
      printf ("0\n");
    }
#endif

  // First allocate clause and copy literals.

  size_t size = literals.size ();
  size_t bytes = sizeof (struct clause) + size * sizeof (int);
  clause * c = (clause*) new char [bytes];

  assert (size <= UINT_MAX);
  c->id = added++;

  constraint_is_clause[c->id] = is_clause;

  assert (clauses.size () <= (size_t) INT_MAX);
  c->size = size;

  c->redundant = redundant;
  c->reason = false;
  c->garbage = false;
  c->used = true;
  c->glue = glue;

  int * q = c->literals;
  for (auto lit : literals)
    *q++ = lit;

  debug (c, is_clause ? "new clause": "new term"); 

  // Save it on global stack of clauses.

  clauses.push_back (c);

  // Connect the clause in any case.

  if (size > 1)
    {
      watch_literal (literals[0], c, is_clause);
      watch_literal (literals[1], c, is_clause);
    }

  if (redundant)
    return c;

  // Handle the special case of empty and unit clauses/terms.

  if (!size)
    {
      debug (c, "parsed empty %s", is_clause ? "clause" : "term");
      empty[is_clause] = c;
    }
  else if (size == 1)
    {
      int unit = literals[0];
      signed char value = values[unit];
      auto disabling = is_clause ? 1 : -1;
      if (!value)
	    assign (is_clause ? unit : -unit, unit_reason);
      else if (value != disabling)
	{
	  debug (c, "inconsistent unit %s", is_clause ? "clause" : "term");
	  empty[is_clause] = c;
	}
    }

  return c;
}

void universal_existential_reduction(std::vector<int>& literals, bool is_clause) {
  std::sort(literals.begin(), literals.end(), [](const int& lit1, const int& lit2) { return abs(lit1) < abs(lit2); } );
  while (!literals.empty() && variable_is_existential(abs(literals.back())) != is_clause) {
    literals.pop_back();
  }
}

static const char * file_name;
static bool close_file;
static FILE * file;

static void
parse_error (const char * fmt, ...)
{
  fprintf (stderr, "solver: parse error in '%s': ", file_name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
parse (void)
{
  int ch;
  int qdimacs_variables;
  while ((ch = getc (file)) == 'c') {
    while ((ch = getc (file)) != '\n')
	    if (ch == EOF)
	      parse_error ("end-of-file in comment");
  }
  if (ch != 'p')
    parse_error ("expected 'c' or 'p'");
  int clauses;
  if (fscanf (file, " cnf %d %d", &qdimacs_variables, &clauses) != 2 ||
      variables < 0 || qdimacs_variables >= INT_MAX ||
      clauses < 0 || clauses >= INT_MAX)
    parse_error ("invalid header");
  printf ("c parsed header 'p cnf %d %d'\n", qdimacs_variables, clauses);
  fpos_t pos;
  int nr_vars = 0;
  for (;;) {
    int var = 0;
    char qtype;
    fgetpos(file, &pos); // Store file position before checking if there's another quantifier block.
    int count = fscanf(file, " %c", &qtype);
    if (count == 0 || (qtype != 'a' && qtype != 'e'))
      break;
    while (fscanf (file, "%d", &var) == 1) {
      if (var < 0 || var > qdimacs_variables)
        parse_error ("invalid variable '%d'", var);
      if (var) {
        nr_vars++;
        int internal_var = (2 * nr_vars) + (qtype == 'e' ? 1 : 0);
        auto var_str = std::to_string(var);
        if (internal_variable_names.find(var_str) != internal_variable_names.end())
          parse_error ("variable '%s' occurring in more than one quantifier block", var_str.c_str());
        original_variable_names[internal_var] = var_str;
        internal_variable_names[var_str] = internal_var;
        if (qtype == 'a' && innermost_universal < internal_var)
          innermost_universal = internal_var;
      } else {
        break;
      }
    }
  }
  variables = nr_vars*2+2; // Double space for variables to represent quantifier types.
  initialize ();
  fsetpos(file, &pos); // Restore file position where no further quantifier block was found.
  std::vector<int> clause;
  int lit = 0, parsed = 0;
  while (fscanf (file, "%d", &lit) == 1)
    {
      if (parsed == clauses)
	parse_error ("too many clauses");
      if (lit == INT_MIN || abs (lit) > variables)
	parse_error ("invalid literal '%d'", lit);
      if (lit) {
        auto var_str = std::to_string((abs(lit)));
        if (internal_variable_names.find(var_str) == internal_variable_names.end())
          parse_error("free variable %s not allowed", var_str.c_str());
        int lit_internal = lit > 0 ? internal_variable_names[var_str] : -internal_variable_names[var_str];
	      clause.push_back (lit_internal);
      } else {
        universal_existential_reduction(clause, true);
        add_clause (false, 0, clause, true);
        clause.clear ();
        parsed++;
      }
    }

  if (lit)
    parse_error ("terminating zero missing");

  if (parsed != clauses)
    parse_error ("clause missing");

  if (close_file)
    fclose (file);
}

static clause *
propagate (bool& is_clause) {
  clause * conflict = 0;
  while (!conflict && propagated != trail.size ()) {
    int lit = trail[propagated++];
    debug ("propagating %s", debug (lit));
    propagations++;

    for (bool is_clause_: {true, false}) {
      int not_lit = is_clause_ ? -lit: lit;
      int disabling_value = is_clause_ ? 1 : -1;

      auto & not_lit_watches = watches[is_clause_][not_lit];
      auto begin_not_lit_watches = not_lit_watches.begin ();
      auto end_not_lit_watches = not_lit_watches.end ();
      auto p = begin_not_lit_watches, q = p;

      while (p != end_not_lit_watches) {
        auto watch = *q++ = *p++;
        int blocking = watch.blocking;
        signed char blocking_value = values[blocking];
        if (blocking_value == disabling_value)
          continue;

        auto clause = watch.clause;

        if (watch.binary) {
          if (blocking_value == -disabling_value) {
            conflict = clause;
            is_clause = is_clause_;
            assert(constraint_is_clause[conflict->id] == is_clause);
            break;
          }

          if (blocking_value == 0 && variable_is_existential(abs(blocking)) != is_clause_) {
            conflict = clause;
            is_clause = is_clause_;
            levels[abs(blocking)] = level; // Required for analyze.
            assert(constraint_is_clause[conflict->id] == is_clause);
            break;
          }

          assign (disabling_value * blocking, clause);
          continue;
        }

        int * literals = clause->literals;

        if (literals[1] != not_lit)
          std::swap (literals[0], literals[1]);

        int other = literals[0];
        signed char other_value = values[other];
        if (other_value == disabling_value)
          continue;

        int * end_literals = literals + clause->size;

        for (int * l = literals + 2; l != end_literals; l++) {
          int replacement = *l;
          signed char value = values[replacement];
          if (value != -disabling_value) {
            q--;
            debug (clause, "unwatching %s in", debug (not_lit));
            std::swap (literals[1], *l);
            watch_literal (replacement, clause, is_clause_);
            goto CONTINUE;
          }
        }

        if (other_value == -disabling_value) {
          conflict = clause;
          is_clause = is_clause_;
          assert(constraint_is_clause[conflict->id] == is_clause);
          break;
        }

        if (other_value == 0 && variable_is_existential(abs(other)) != is_clause_) {
          conflict = clause;
          is_clause = is_clause_;
          levels[abs(other)] = level; // Required for analyze.
          assert(constraint_is_clause[conflict->id] == is_clause);
          break;
        }

        assign (disabling_value * other, clause);
        CONTINUE:
          ;
      }

      while (p != end_not_lit_watches)
        *q++ = *p++;

      if (q != end_not_lit_watches)
        not_lit_watches.resize (q - begin_not_lit_watches);
    }
  }
    
  if (conflict) {
    debug (conflict, "conflicting %s", is_clause ? "clause" : "term");
    conflicts++;
    assert(constraint_is_clause[conflict->id] == is_clause);
  }

  return conflict;
}

static void
update_watched_dependencies (void) {
  while (dependencies_propagated != trail.size ()) {
    auto idx = abs(trail[dependencies_propagated++]);
    auto& variables_watched = deps_watching[idx];
    auto p = variables_watched.begin(), q = p;
    while (p != variables_watched.end()) {
      auto watched = *p++;
      if (values[watched]) {
        *q++ = watched;
        continue;
      }
      if (deps[watched].front() != idx) // spurious entry
        continue;
      // Try to find new watched dependency.
      auto r = ++deps[watched].begin();
      for (; r != deps[watched].end() && values[*r]; r++);
      if (r != deps[watched].end()) {
        deps_watching[*r].push_back(watched);
        deps[watched].front() = *r;
        *r = idx;
      } else {
        // No watcher found, variable is eligible for assignment. Update search if necessary.
        *q++ = watched;
        debug("variable %s eligible for assignment after assigning %s", debug(watched), debug(idx));
        link * link = links + watched;
        if (!search || search->stamp < link->stamp)
          search = link;
      }
    }
    if (q != variables_watched.end())
        variables_watched.resize(q - variables_watched.begin());
  }
}

static void
set_initial_term (void)
{
  auto& size = initial_term->size;
  size = 0;
  for (auto clause: clauses) {
    if (clause->redundant)
      continue;
    for (auto lit: *clause)
      if (values[lit] > 0) {
        auto var = abs(lit);
        if (!seen[var] && var <= innermost_universal) {
          initial_term->literals[size++] = lit;
          seen[var] = true;
        }
        break;
      }
  }
  std::sort(initial_term->literals, initial_term->literals + size, 
    [](const int& lit1, const int& lit2) { return abs(lit1) < abs(lit2); } );
  for (auto lit: *initial_term) {
    auto var = abs(lit);
    seen[var] = false;
  }
  for (; size && variable_is_existential(abs(initial_term->literals[size-1])); size--);
}

static int
decide (void)
{
  decisions++;
  update_watched_dependencies();

  int decision = 0;

  while (search->prev && (values[decision = search - links] || (deps[decision].size() && !values[deps[decision].front()])))
    search = search->prev;

  if (phases[decision])
    decision = -decision;

  debug ("decision %s with stamp %zu", debug (decision), search->stamp);

  assert (level == control.size ());
  assert (level == level_occs.size() - 1);
  control.push_back (trail.size ());
  level_occs.push_back(0);
  level++;

  return decision;
}

static void
unassign (int lit, unsigned jump)
{
  debug ("unassign %s", debug (lit));
  assert (values[lit] > 0);
  assert (values[-lit] < 0);
  values[lit] = values[-lit] = 0;
  link * link = links + abs (lit);
  auto& ds = deps[abs(lit)];
  if ((!withQuantifierRearrange || isOriginalVariable(abs(lit)))
      && (!search || (search->stamp < link->stamp && (ds.empty() || levels[ds.front()] <= jump))))
    search = link;
}

static void
backtrack (unsigned jump)
{
  assert (jump < level);
  assert (control.size () == level);

  debug ("backtracking to level %u", jump);
  while (control.size () != jump)
    {
      debug ("unassigning literals on level %zu", control.size ());

      size_t previous =  control.back ();
      control.pop_back ();
      level_occs.pop_back();

      while (trail.size () > previous)
	{
	  int lit = trail.back ();
	  trail.pop_back ();
	  unassign (lit, jump);
	}

      level--;
    }
  propagated = trail.size ();
  dependencies_propagated = trail.size();
  assert (level == jump);
}

static int
minimize (int lit, unsigned int asserting_level, bool is_clause, int depth = 0)
{
  if (depth > 1000)
    return 0; // 0 is "poison".
  int idx = abs (lit);
  if (depth && seen[idx])
    return INT_MAX;
  if (minimizable[idx] > -1)
    return minimizable[idx];
  if (levels[idx] == asserting_level)
    return 0;
  if (variable_is_existential(idx) != is_clause)
    return idx;
  clause * reason = reasons[idx];
  if (!reason)
    return 0;
  int res = INT_MAX;
  for (auto other : *reason)
    if (abs(other) != idx) {
      res = std::min(res, minimize (other, asserting_level, is_clause, depth + 1));
	    if (!res)
	      break;
    }
  minimizable[idx] = res;
  minimized.push_back (idx);
  return res;
}

struct minimize_compare
{
  minimize_compare(unsigned int alevel, bool is_clause): alevel(alevel), is_clause(is_clause) {}
  unsigned int alevel;
  bool is_clause;
  bool operator () (int a, int b) {
    auto ca = minimize(a, alevel, is_clause);
    auto cb = minimize(b, alevel, is_clause);
    return (ca < cb || (ca == cb && abs(a) > abs(b)));
  }
};

static void
minimize (bool is_clause)
{
  debug ("minimizing first UIP clause of size %zu" , learn.size ());
  // We assume that the first literal is asserting.
  auto alevel = levels[abs(learn.front())];
  deduced += learn.size ();
  auto begin = learn.begin ();
  auto end = learn.end ();
  auto p = begin, q = p;
  int innermost = abs(*p);
  std::sort(begin + 1, end, minimize_compare(alevel, is_clause));
  for (p = begin; p != end; p++)
    if (minimize(*p, alevel, is_clause) < innermost) {
      *q++ = *p;
      if (variable_is_existential(abs(*p)) == is_clause && innermost < abs(*p))
        innermost = abs(*p);
    }
  learn.resize (q - begin);
  debug ("minimized first UIP clause of size %zu" , learn.size ());
  learned += learn.size ();
  for (auto idx : minimized)
    minimizable[idx] = -1;
  minimized.clear ();
}

struct stamped_earlier
{
  bool operator () (int a, int b) {
    return links[a].stamp < links[b].stamp;
  }
};

static void
cleanup (void)
{
  analyzed.clear ();
  for (auto lit: learn) {
    auto var = abs(lit);
    seen[var] = false;
    level_occs[levels[var]] = 0;
  }
  learn.clear ();
}

static bool
analyze (clause * reason, bool is_clause)
{
  if (!level)
    return false;
  assert (analyzed.empty ());
  assert (learn.empty ());
  size_t t = trail.size ();
  int leftmost_blocked = 0;
  int pivot = 0;
  auto plevel = level;

  // Phase 1: Find asserting literal.
  for (;;) {
    for (auto lit: *reason) {
      auto var = abs(lit);
      if (var == abs(pivot) || seen[var])
          continue;
      analyzed.push_back(var);
      learn.push_back(lit);
      seen[var] = true;
      auto var_level = levels[var];
      if (variable_is_existential(var) == is_clause) {
        level_occs[var_level]++;
      } else
        if (var_level >= plevel && (leftmost_blocked == 0 || var < leftmost_blocked))
          leftmost_blocked = var;
    }
    // Find next pivot. Pivots must be existential for clauses and universal for terms.
    do {
      assert (t);
      pivot = trail[--t];
    } while (t && (!seen[abs(pivot)] || variable_is_existential(abs(pivot)) != is_clause));
    if ((!t && (!seen[abs(pivot)] || variable_is_existential(abs(pivot)) != is_clause)) || levels[abs(pivot)] == 0) {
      // Learned clause/term is empty.
      learn.clear();
      return false;
    }
    assert(seen[abs(pivot)] && variable_is_existential(abs(pivot)) == is_clause);
    if (plevel > levels[abs(pivot)]) {
      // Upon traversing decision levels, re-compute leftmost blocked variable.
      // TODO: Here it would be easy to apply universal/existential reduction.
      leftmost_blocked = 0;
      for (auto lit: learn) {
        if (variable_is_existential(abs(lit)) != is_clause &&
            levels[abs(lit)] >= levels[abs(pivot)] && 
            (leftmost_blocked == 0 || abs(lit) < leftmost_blocked))
          leftmost_blocked = abs(lit);
      }
    }
    plevel = levels[abs(pivot)];
    if (level_occs[plevel] == 1 && (!leftmost_blocked || abs(pivot) < leftmost_blocked))
      break; // Pivot is the asserting literal.
    // Must resolve further at pivot.
    reason = reasons[abs(pivot)];
    if (reason == decision_reason) {
      debug ("out of order decision: %s", debug(pivot));
      debug ("blocked: %s", debug(leftmost_blocked));
      assert(leftmost_blocked);
      cleanup();
      unsigned jump = levels[abs(pivot)] - 1;
      assert(jump >= 0);
      backtrack(jump);
      dependencies++;
      auto& ds = deps[abs(pivot)];
      assert(std::find(ds.begin(), ds.end(), leftmost_blocked) == ds.end());
      ds.push_back(leftmost_blocked);
      std::swap(ds.front(), ds.back());
      deps_watching[leftmost_blocked].push_back(abs(pivot));
      return true;
    }
    debug (reason, "reason %s", is_clause ? "clause" : "term");
    seen[abs(pivot)] = false;
    level_occs[plevel]--;
  }
  auto asserting = is_clause ? -pivot: pivot;
  debug ("asserting literal %s", debug(asserting));
  // Phase 2: Remove remaining existentials blocking reduction of leftmost blocked.
  if (leftmost_blocked) {
    for (;;) {
      // Find next pivot blocking leftmost blocked.
      while (t && (!seen[abs(pivot)] || variable_is_existential(abs(pivot)) != is_clause || abs(pivot) < leftmost_blocked)) {
        pivot = trail[--t];
      }
      if (!t && (!seen[abs(pivot)] || variable_is_existential(abs(pivot)) != is_clause || abs(pivot) < leftmost_blocked))
        break; // No blocking existentials/universal where found.
      // Resolve further at pivot.
      reason = reasons[abs(pivot)];
      if (reason == decision_reason) {
        debug ("out of order decision: %s", debug(pivot));
        debug ("blocked: %s", debug(leftmost_blocked));
        assert(leftmost_blocked);
        cleanup();
        unsigned jump = levels[abs(pivot)] - 1;
        assert(jump >= 0);
        backtrack(jump);
        dependencies++;
        auto& ds = deps[abs(pivot)];
        assert(std::find(ds.begin(), ds.end(), leftmost_blocked) == ds.end());
        ds.push_back(leftmost_blocked);
        std::swap(ds.front(), ds.back());
        deps_watching[leftmost_blocked].push_back(abs(pivot));
        return true;
      }
      seen[abs(pivot)] = false;
      level_occs[plevel]--;
      // Visit reason clause/term.
      for (auto lit: *reason) {
        auto var = abs(lit);
        if (var == abs(pivot) || seen[var])
          continue;
        analyzed.push_back(var);
        learn.push_back(lit);
        seen[var] = true;
      }
    }
  }
  // Compute literals remaining in learned clause.
  auto p = learn.begin(), q = p;
  for (; p != learn.end(); p++) {
    auto var = abs(*p);
    if (seen[var]) {
      *q++ = *p;
      level_occs[levels[var]] = 0; // Reset level occurrences array.
    }
  }
  learn.resize(q - learn.begin());
  universal_existential_reduction(learn, is_clause);
  if (learn.empty())
    return false;
  // Find asserting literal and swap with literal at index 0.
  for (p = learn.begin(); p != learn.end() && *p != asserting; p++);
  assert(p != learn.end());
  *p = learn.front();
  learn.front() = asserting;
  minimize (is_clause);
  // Compute backtrack level and glue.
  unsigned jump = 0;
  unsigned glue = 0;
  unsigned pulled = ++stamp;
  q = learn.begin() + 1;
  for (p = q; p != learn.end(); p++) {
    auto tmp = levels[abs(*p)];
    if (tmp > jump) {
      jump = tmp;
      std::swap (*q, *p);
    }
    if (stamps[tmp] != pulled) { // Compute Glucose level.
      stamps[tmp] = pulled;
      glue++;
    }
  }
  debug ("first UIP %s", debug (asserting));
  debug ("glucose level %u", glue);
  slow_glue_average += 1e-5 * (glue - slow_glue_average);
  fast_glue_average += 0.03 * (glue - fast_glue_average);
  struct clause * learned = add_clause (true, glue, learn, is_clause);
  assert (asserting);
  debug ("flipping %s", debug (asserting));
  backtrack (jump);
  assign (is_clause ? asserting : -asserting, learned);
  for (auto idx : analyzed)
    seen[idx] = false;
  std::sort (analyzed.begin (), analyzed.end (), stamped_earlier ());
  for (auto idx : analyzed)
    if(!withQuantifierRearrange || isOriginalVariable(idx))
      dequeue (idx), enqueue (idx, !values[idx]);
  analyzed.clear ();
  learn.clear ();
  return true;
}

static void
mark_reason_clauses (bool mark)
{
  for (auto lit : trail)
    {
      int idx = abs (lit);
      clause * clause = reasons[idx];
      if (clause == unit_reason)
	continue;
      if (clause == decision_reason)
	continue;
      assert (clause->reason != mark);
      clause->reason = mark;
    }
}

static std::vector<clause*>
gather_reduce_candidates (void)
{
  std::vector<clause*> candidates;
  mark_reason_clauses (true);
  for (auto clause : clauses)
    {
      if (clause->reason)
	continue;
      if (!clause->redundant)
	continue;
      if (clause->glue <= 2)
	continue;
      bool used = clause->used;
      clause->used = false;
      if (used)
	continue;
      candidates.push_back (clause);
    }
  mark_reason_clauses (false);
  return candidates;
}

struct less_relevant
{
  bool operator () (clause * a, clause * b) {
    if (a->glue < b->glue)
      return false;
    if (a->glue > b->glue)
      return true;
    if (a->size < b->size)
      return false;
    if (a->size > b->size)
      return true;
    return a->id < b->id;
  }
};

static void
mark_garbage (std::vector<clause*> & candidates)
{
  size_t target = reduce_fraction * candidates.size ();
  size_t marked = 0;
  for (auto clause : candidates)
    if (marked++ == target)
      break;
    else
      {
	debug (clause, "garbage");
	clause->garbage = true;
      }
  debug ("marked %zu clauses as garbage", marked);
}

static void
flush_garbage_watches (void)
{
  for (int lit = -variables; lit <= variables; lit++)
    if (lit) {
      for (int i = 0; i <= 1; i++) {
        auto & lit_occurrences = watches[i][lit];
        auto begin = lit_occurrences.begin ();
        auto end = lit_occurrences.end ();
        auto p = begin, q = p;
        while (p != end)
          {
            auto watch = *p++;
            if (!watch.clause->garbage)
              *q++ = watch;
          }
        lit_occurrences.resize (q - begin);
      }
    }
}

static void
recycle_garbage_clauses (void)
{
  auto begin = clauses.begin ();
  auto end = clauses.end ();
  auto p = begin, q = p;
  while (p != end)
    {
      auto clause = *p++;
      if (clause->garbage)
	{
	  delete_clause (clause);
	  recycled++;
	}
      else
	*q++ = clause;
    }
  clauses.resize (q - begin);
}

static double process_time (void);

static void
report (char type)
{
  printf ("c %c %.2f %zu %zu %zu %zu %zu %.2f\n",
          type, process_time (),
          reductions, restarts, conflicts, dependencies, clauses.size (),
	  slow_glue_average);
  fflush (stdout);
}

static void
reset_dependencies (void)
{
  link * link = queue.first;
  while (link) {
    auto idx = link - links;
    deps[idx].clear();
    deps_watching[idx].clear();
    if (!search || search->stamp < link->stamp)
      search = link;
    link = link->next;
  }
}

static void
reduce (void)
{
  next.reduce = conflicts + reduce_interval * ++reductions;
  debug ("clause data-base reduction %zu", reductions);
  auto candidates = gather_reduce_candidates ();
  std::sort (candidates.begin (), candidates.end (), less_relevant ());
  mark_garbage (candidates);
  flush_garbage_watches ();
  recycle_garbage_clauses ();
  report ('-');
  reset_dependencies();
}

static void
restart (void)
{
  next.restart = conflicts + restart_interval;
  restarts++;
  debug ("restart %zu after %zu conflicts", restarts, conflicts);
  backtrack (0);
}

// Return value of '10' is the exit code for 'satisfiable' formula and '20'
// is the exit code for 'unsatisfiable' formula in the SAT competition.

// We use the same encoding for the return value of the 'solve' routine.
// Any other value (like '0') is considered 'unknown' and ignored.

static const int satisfiable = 10;
static const int unsatisfiable = 20;

static int
cdcl (void)
{
  for (;;) {
    bool is_clause;
    clause * conflict = propagate(is_clause);
    if (!conflict && trail.size () == original_variable_names.size()) {
      set_initial_term();
      conflict = initial_term;
      is_clause = false;
      conflicts++;
    }
    if (conflict) {
      if (!analyze(conflict, is_clause))
        return is_clause ? unsatisfiable : satisfiable;
      continue;
    }
    if (level && next.restart < conflicts && 1.2 * slow_glue_average < fast_glue_average)
      restart ();
    if (next.reduce < conflicts)
      reduce ();
    int lit = decide ();
    assign (lit, decision_reason);
  }
}

int
solve (void)
{
  if (empty[true])
    return unsatisfiable;
  if (empty[false])
    return satisfiable;
  next.reduce = reduce_interval;
  debug ("initial reduce limit of %zu conflicts", next.reduce);
  next.restart = restart_interval;
  debug ("initial restart limit of %zu conflicts", next.restart);
  return cdcl ();
}

// Printing the model in the format of the SAT competition, e.g.,
//
//   v -1 2 3 0
//
// Always prints a full assignments even if not all values are set.

static void
print_model (void)
{
  printf ("v ");
  for (int idx = 1; idx <= variables; idx++)
    {
      if (values[idx] < 0)
	printf ("-");
      printf ("%d ", idx);
    }
  printf ("0\n");
}

// Get process-time of this process.  This is not portable to Windows but
// should work on other Unixes such as MacOS as is.

#include <sys/time.h>
#include <sys/resource.h>

static double
process_time (void)
{
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static bool witness = true;

static bool useQcirParser = false;

static bool quantifierRearrange = false;

int
main (int argc, char ** argv)
{
  for (int i = 1; i != argc; i++)
    {
      const char * arg = argv[i];
      if (!strcmp (arg, "-h") || !strcmp (arg, "--help"))
	{
	  fputs (usage, stdout);
	  exit (0);
	}
      else if (!strcmp (arg, "-l") || !strcmp (arg, "--logging"))
#ifdef LOGGING
	logging = true;
#else
        die ("compiled without logging code (use './configure --logging')");
#endif
      else if (!strcmp (arg, "-n") || !strcmp (arg, "--no-witness"))
	witness = false;
      else if (!strcmp (arg, "--qcir"))
  useQcirParser = true;
  else if (!strcmp (arg, "-r"))
  quantifierRearrange = true;
      else if (arg[0] == '-')
	die ("invalid option '%s' (try '-h')", arg);
      else if (file_name)
	die ("too many arguments '%s' and '%s' (try '-h')",
	     file_name, arg);
      else
	file_name = arg;
    }

  if (!file_name)
    {
      file_name = "<stdin>";
      assert (!close_file);
      file = stdin;
    }
  else if (!(file = fopen (argv[1], "r")))
    die ("could not open and read '%s'", file_name);
  else
    close_file = true;

  if(useQcirParser){
    message("Running QCIR-Parser");
    message("reading from '%s'", file_name);
    runParser(file_name, quantifierRearrange);
  } else {
  message ("Simple but Complete QCDCl QBF Solver");
  message ("reading from '%s'", file_name);
  parse ();
  }

  int res = solve ();

  if (res == 10)
    {
      printf ("s SATISFIABLE\n");
      if (witness)
	      print_model ();
    }
  else if (res == 20)
    printf ("s UNSATISFIABLE\n");

  release ();

  printf ("c %-30s %16zu\n", "reductions:", reductions);
  printf ("c %-30s %16zu\n", "restarts:", restarts);
  printf ("c %-30s %16zu\n", "conflicts:", conflicts);
  printf ("c %-30s %16zu\n", "dependencies:", dependencies);
  printf ("c %-30s %16zu\n", "decisions:", decisions);
  printf ("c %-30s %16zu\n", "propagations:", propagations);
  printf ("c %-30s %16zu\n", "recycled-clauses:", recycled);
  printf ("c %-30s %16.2f\n", "average-learned-clause-size:",
          conflicts ? (double) learned / conflicts : 0.0);
  printf ("c %-30s %16.2f %%\n", "minimized-literals:",
          deduced ? 100.0 * (deduced - learned) / deduced : 0);
  printf ("c %-30s %16.2f seconds\n", "process-time:", process_time ());
  printf ("c exit code %d\n", res);
  return res;
}
