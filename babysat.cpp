// clang-format off

const char *usage =
"usage: babysat [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' can be one of the following\n"
"\n"
"  -h | --help        print this command line option summary\n"
#ifdef LOGGING
"  -l | --logging     print very verbose logging information\n"
#endif
"  -q | --quiet       do not print any messages\n"
"  -n | --no-witness  do not print witness if satisfiable\n"
"  -v | --verbose     print verbose messages\n"
"\n"
"and '<dimacs>' is the input file in DIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n";

// clang-format on

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <set>
#include <vector>

#include <iostream>

// Linux/Unix system specific.

#include <sys/resource.h>
#include <sys/time.h>

// Global options accessible through the command line.

static bool witness = true;

static int verbosity; // -1=quiet, 0=normal, 1=verbose, INT_MAX=logging

// Global options fixed at compile time.

struct Counter {
  unsigned count; // Number of non-false literals left.
  int sum; // Sum of non-false literals.
};

#define FALSE_ASSIGNMENT -1
#define TRUE_ASSIGNMENT 1
#define UNASSIGNED 0

//#define HeuristicsTest

static int variables;       // Variable range: 1,..,<variables>
static signed char *values; // Assignment 0=unassigned,-1=false,1=true.
static unsigned *levels;    // Maps variables to their level;

static std::vector<Counter *> clause_counters;
static std::vector<Counter *> *matrix_counters;

static Counter *empty_counter; // Empty counter found.

// static std::vector<int> trail;
static int *trail;
static int *assigned;
static int *propagated;
static std::vector<int *> control;

static unsigned level;    // Decision level.

static size_t limit = -1;

// Statistics:

static size_t added;        // Number of added clauses.
static size_t conflicts;    // Number of conflicts.
static size_t decisions;    // Number of decisions.
static size_t propagations; // Number of propagated literals.
static size_t reports;      // Number of calls to 'report'.
static int fixed;           // Number of root-level assigned variables.

// Get process-time of this process.  This is not portable to Windows but
// should work on other Unixes such as MacOS as is.

static double process_time(void) {
  struct rusage u;
  double res;
  if (getrusage(RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// Report progress once in a while.

static void report(char type) {
  if (verbosity < 0)
    return;
  if (!(reports++ % 20))
    printf("c\n"
           "c             decisions             variables\n"
           "c   seconds              conflicts            remaining\n"
           "c\n");
  int remaining = variables - fixed;
  printf("c %c %7.2f %11zu %11zu %9d %3.0f%%\n", type, process_time(),
         decisions, conflicts, remaining,
         variables ? 100.0 * remaining / variables : 0);
  fflush(stdout);
}

// Generates nice compiler warnings if format string does not fit arguments.

static void message(const char *, ...) __attribute__((format(printf, 1, 2)));
static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void parse_error(const char *fmt, ...)
    __attribute__((format(printf, 1, 2)));

#ifdef LOGGING

static void debug(const char *, ...) __attribute__((format(printf, 1, 2)));

static void debug(Clause *, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static bool logging() { return verbosity == INT_MAX; }

// Print debugging message if '--debug' is used.  This is only enabled
// if the solver is configured with './configure --logging' (which is the
// default for './configure --debug').  Even if logging code is included
// this way, it still needs to be enabled at run-time through '-l'.

static char debug_buffer[4][32];
static size_t next_debug_buffer;

// Get a statically allocate string buffer.
// Used here only for printing literals.

static char *debug_string(void) {
  char *res = debug_buffer[next_debug_buffer++];
  if (next_debug_buffer == sizeof debug_buffer / sizeof *debug_buffer)
    next_debug_buffer = 0;
  return res;
}

static char *debug(int lit) {
  if (!logging())
    return 0;
  char *res = debug_string();
  sprintf(res, "%d", lit);
  int value = values[lit];
  if (value) {
    size_t len = strlen(res);
    size_t remaining = sizeof debug_buffer[0] - len;
    snprintf(res + len, remaining, "@%u=%d", levels[abs(lit)], level);
  }
  assert(strlen(res) <= sizeof debug_buffer[0]);
  return res;
}

static void debug_prefix(void) { printf("c DEBUG %u ", level); }

static void debug_suffix(void) {
  fputc('\n', stdout);
  fflush(stdout);
}

static void debug(const char *fmt, ...) {
  if (!logging())
    return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  debug_suffix();
}

static void debug(Clause *c, const char *fmt, ...) {
  if (!logging())
    return;
  debug_prefix();
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf(" size %u clause[%u]", c->size, c->id);
  for (auto lit : *c)
    printf(" %s", debug(lit));
  debug_suffix();
}

#else

#define debug(...)                                                             \
  do {                                                                         \
  } while (0)

#endif

// Print message to '<stdout>' and flush it.

static void message(const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void line() {
  if (verbosity < 0)
    return;
  fputs("c\n", stdout);
  fflush(stdout);
}

static void verbose(const char *fmt, ...) {
  if (verbosity <= 0)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

// Print error message and 'die'.

static void die(const char *fmt, ...) {
  fprintf(stderr, "babysat: error: ");
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void initialize(void) {
  assert(variables < INT_MAX);
  unsigned size = variables + 1;

  unsigned twice = 2 * size;

  values = new signed char[twice];
  matrix_counters = new std::vector<Counter *>[twice];

  levels = new unsigned[size];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).
  values += variables;
  matrix_counters += variables;

  propagated = assigned = trail = new int[size];
  assert(!level);
}

static void delete_counter(Counter *c) {
  delete[] c;
}

static void release(void) {
  delete[] trail;

  values -= variables;

  matrix_counters -= variables;

  delete[] values;

  delete[] matrix_counters;

  delete[] levels;
}

// Check whether all clauses are satisfied.

static bool satisfied() {
  return assigned - trail == variables;
}

static void assign(int lit) {
  debug("assign %s", debug(lit));
  values[lit] = TRUE_ASSIGNMENT;
  values[-lit] = FALSE_ASSIGNMENT;
  *assigned++ = lit;
  levels[abs(lit)] = level;
  if (!level)
    fixed++;

  #ifdef HeuriticsTest
  lit_occurrences[abs(lit)] = 0;
  #endif
  // Set 'values[lit]' and 'values[-lit]'.
  // Set 'levels[abs(lit)]'.
  // Push literal on trail.
  // If root-level (so level == 0) increase fixed.
}

static void connect_literal(int lit, Counter *c) {
  matrix_counters[lit].push_back(c);
}

static Counter *add_clause(std::vector<int> &literals) {
  size_t size = literals.size();
  size_t bytes_counter = sizeof(struct Counter) + size * sizeof(int);
  Counter *counter = (Counter *)new char[bytes_counter];

  counter->count = 0;
  counter->sum = 0;

  for (auto lit : literals) {
    counter->sum += lit;
    counter->count++;
    connect_literal(lit, counter);
  }

  debug(c, "new");

  clause_counters.push_back(counter);

  // Handle the special case of empty and unit clauses.
  if (!size) {
    debug(c, "parsed empty clause");
    empty_counter = counter;
  } else if (size == 1) {
    int unit = literals[0];
    signed char value = values[unit];
    if (!value) {
      assign(unit);
    }
    else if (value < 0) {
      debug(c, "inconsistent unit clause");
      empty_counter = counter;
    }
  }

  return counter;
}

static const char *file_name;
static bool close_file;
static FILE *file;

static void parse_error(const char *fmt, ...) {
  fprintf(stderr, "babysat: parse error in '%s': ", file_name);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void parse(void) {
  int ch;
  while ((ch = getc(file)) == 'c') {
    while ((ch = getc(file)) != '\n')
      if (ch == EOF)
        parse_error("end-of-file in comment");
  }
  if (ch != 'p')
    parse_error("expected 'c' or 'p'");
  int clauses;
  if (fscanf(file, " cnf %d %d", &variables, &clauses) != 2 || variables < 0 ||
      variables >= INT_MAX || clauses < 0 || clauses >= INT_MAX)
    parse_error("invalid header");
  message("parsed header 'p cnf %d %d'", variables, clauses);
  initialize();
  std::vector<int> clause;
  int lit = 0, parsed = 0;
  size_t literals = 0;
  while (fscanf(file, "%d", &lit) == 1) {
    if (parsed == clauses)
      parse_error("too many clauses");
    if (lit == INT_MIN || abs(lit) > variables)
      parse_error("invalid literal '%d'", lit);
    if (lit) {
      clause.push_back(lit);
      literals++;
    } else {
      add_clause(clause);
      clause.clear();
      parsed++;
    }
  }
  if (lit)
    parse_error("terminating zero missing");
  if (parsed != clauses)
    parse_error("clause missing");
  if (close_file)
    fclose(file);
  verbose("parsed %zu literals in %d clauses", literals, parsed);
}



// Return 'false' if propagation detects an empty clause otherwise if it
// completes propagating all literals since the last time it was called
// without finding an empty clause it returns 'true'.  Beside finding
// conflict propagating a literal also detects unit clauses and
// then assign the forced literal by that unit clause.

static bool propagate(void) {
  while (propagated != assigned) {
    int lit = *propagated++;
    propagations++;
    bool conflict = false;
    for (auto c : matrix_counters[-lit]) {
      if(values[-lit] == 0) break;
      c->sum -= -lit;
      c->count--;
      if (c->count == 1){
        if (values[c->sum] == 0) assign(c->sum);
        if (values[c->sum] == -1) { 
          conflicts++;
          conflict = true; // return false;
        }
        if (values[c->sum] == 1) continue;
        }
      if (c->count == 0 && c->sum == 0) {
        conflicts++; 
        conflict = true; // return false;
      }
    }
    if (conflict) return false; // was not there before
  }
  return true;
}

static void unpropagate(void) {
  int * control_index = control.back();
  while (propagated != control_index) {
    int lit = *--propagated;
    for (auto c : matrix_counters[-lit]) {
      c->sum += -lit;
      c->count++;
    }
  }
}

static int is_power_of_two(size_t n) { return n && !(n & (n - 1)); }


static int decide(void) {
  if (*assigned == variables)
  return 0;
  decisions++;
  int res = 1;
  // simply choose the first unassigned variable
  while (assert(res <= variables), values[res])
    res++;
  /*int highest_unassigned = 0;
  int lit = 0;
  for (auto c : matrix_counters[res]) {
    if (c->count >= highest_unassigned && values[res] == 0) {
      lit = res;
      highest_unassigned = c->count;
    }
    res++;
    if (res > variables) break;
  }
  res = lit;*/
  level++;
  control.push_back(assigned);
  assign(res);
  // Find a variable/literal which is not assigned yet.
  // Increase decision level.
  // Save the current trail on the control stack for backtracking.
  // Assign the picked decision literal.
  if (is_power_of_two(decisions))
    report('d');
  return res;
}

static void unassign(int lit) {
  debug("unassign %s", debug(lit));
  values[lit] = UNASSIGNED;
  values[-lit] = UNASSIGNED;
  // Reset 'values[lit]' and 'values[-lit]'.
}

static void backtrack() {
  // std::cout << level << std::endl;
  assert(level);
  debug("backtracking to level %d", level - 1);
  int *before = control.back();
  unpropagate();
  control.pop_back();
  while (assigned != before) unassign(*--assigned);
  propagated = before;
  level--;
}

// The SAT competition standardized exit codes (the 'exit (code)' or 'return
// res' in 'main').  All other exit codes denote unsolved or error.
static const int unknown = 0;        // Exit code for unknown.
static const int satisfiable = 10;   // Exit code for satisfiable and
static const int unsatisfiable = 20; // unsatisfiable formulas.

#ifdef HeuristicsTest

static void countOccurences(void) {
  lit_occurrences.push_back(0);
  for (int i = 1; i < variables; i++) {
      lit_occurrences.push_back(matrix[i].size());
  }
}
#endif

static int dpll(void) {
  for (;;) {
    if (!propagate()) return unsatisfiable;
    if (limit >= 0 && conflicts >= limit) return unknown;
    if (satisfied()) return satisfiable;
    int x = decide();
    if (dpll() == satisfiable) return satisfiable;
    backtrack();
    assign(-x);
  }
}

static int solve(void) {

  #ifdef HeuristicsTest
  countOccurences();
  #endif

  if (empty_counter)
    return unsatisfiable;
  return dpll();
}

// Checking the model on the original formula is extremely useful for
// testing and debugging.  This 'checker' aborts if an unsatisfied clause is
// found and prints the clause on '<stderr>' for debugging purposes.

static void check_model(void) {
  debug("checking model");
  /*for (auto c : clauses) {
    if (satisfied(c))
      continue;
    fputs("babysat: unsatisfied clause:\n", stderr);
    for (auto lit : *c) {
      fprintf(stderr, "%d ", lit);
      //fprintf(stderr, "%d " , values[lit]);
    }
    fputs("0\n", stderr);
    fflush(stderr);
    abort();
    exit(1);
  }*/
  for (int i = variables; i > 0; i--) {
    if (values[i] == 0) {
      fputs("babysat: unassigned clauses:\n", stderr);
      fprintf(stderr, "%d ", i);
      fprintf(stderr, "%d " , values[i]);
      fputs("0\n", stderr);
      fflush(stderr);
      abort();
      exit(1);
    }
  }
}

// Printing the model in the format of the SAT competition, e.g.,
//
//   v -1 2 3 0
//
// Always prints a full assignments even if not all values are set.

static void print_model(void) {
  printf("v ");
  for (int idx = 1; idx <= variables; idx++) {
    if (values[idx] < 0)
      printf("-");
    printf("%d ", idx);
  }
  printf("0\n");
}

static double average(double a, double b) { return b ? a / b : 0; }

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static void print_statistics() {
  double t = process_time();
  printf("c %-15s %16zu %12.2f per second\n", "conflicts:", conflicts,
         average(conflicts, t));
  printf("c %-15s %16zu %12.2f per second\n", "decisions:", decisions,
         average(decisions, t));
  printf("c %-15s %16zu %12.2f million per second\n",
         "propagations:", propagations, average(propagations * 1e-6, t));
  printf("c\n");
  printf("c %-15s %16.2f seconds\n", "process-time:", t);
}

#include "config.hpp"

int main(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-l") || !strcmp(arg, "--logging"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die("compiled without logging code (use './configure --logging')");
#endif
    else if (!strcmp(arg, "-q") || !strcmp(arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose"))
      verbosity = 1;
    else if (!strcmp(arg, "-n") || !strcmp(arg, "--no-witness"))
      witness = false;
    else if (!strcmp(arg, "-c")) {
      if (++i == argc) die("argument to '-c' missing");
      limit = atoi(argv[i]);
    }
    else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (file_name)
      die("too many arguments '%s' and '%s' (try '-h')", file_name, arg);
    else
      file_name = arg;
  }

  if (!file_name) {
    file_name = "<stdin>";
    assert(!close_file);
    file = stdin;
  } else if (!(file = fopen(file_name, "r")))
    die("could not open and read '%s'", file_name);
  else
    close_file = true;

  message("BabySAT DPLL SAT Solver");
  line();
  message("Copyright (c) 2022-2023, Timo Müller");
  message("Version %s %s", VERSION, GITID);
  message("Compiled with '%s'", BUILD);
  line();
  message("reading from '%s'", file_name);

  parse();
  report('*');

  int res = solve();
  // Print *matrix into a readable format
  /*std::cout << "print start" << std::endl;
  for (auto clause : matrix[-4]) {
    for (auto lit : *clause) {
      std::cout << lit << " ";
    }
    std::cout << "SIZE: " << clause->size << std::endl;
    std::cout << std::endl;
  }
  std::cout << "print end" << std::endl;*/
  report(res == 10 ? '1' : res == 20 ? '0' : '?');
  line();

  if (res == 10) {
    check_model();
    printf("s SATISFIABLE\n");
    if (witness)
      print_model();
  } else if (res == 20)
    printf("s UNSATISFIABLE\n");

  release();

  if (verbosity >= 0)
    line(), print_statistics(), line();

  message("exit code %d", res);

  return res;
}
