#include "cadical.hpp"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

struct Dimacs {
  int variables = 0;
  long long clauses = 0;
  std::vector<std::string> lines;
};

enum class TerminalKind {
  NONE,
  BCP_UNSAT,
  LOOKAHEAD_UNSAT,
  SATISFIED,
  NO_SPLIT,
};

const char *terminal_name(TerminalKind kind) {
  switch (kind) {
  case TerminalKind::NONE:
    return "LIVE";
  case TerminalKind::BCP_UNSAT:
    return "BCP_UNSAT";
  case TerminalKind::LOOKAHEAD_UNSAT:
    return "LOOKAHEAD_UNSAT";
  case TerminalKind::SATISFIED:
    return "SATISFIED";
  case TerminalKind::NO_SPLIT:
    return "NO_SPLIT";
  }
  throw std::runtime_error("invalid terminal kind");
}

struct ProbeResult {
  TerminalKind terminal = TerminalKind::NONE;
  int suggested_split = 0;
  int bcp_fixed = 0;
  int fixed = 0;
  int active = 0;
  int64_t irredundant = 0;
  long long probe_microseconds = 0;
  std::vector<signed char> fixed_values;
  std::vector<int> positive_occurrences;
  std::vector<int> negative_occurrences;

  bool live() const { return terminal == TerminalKind::NONE; }
};

struct BcpProbe {
  bool conflict = false;
  bool satisfied = false;
  int fixed = 0;
  int active = 0;
  int64_t irredundant = 0;
};

struct CandidateEvaluation {
  int variable = 0;
  bool is_lookahead_variable = false;
  bool is_physical_variable = false;
  int occurrence_balance = 0;
  int occurrence_total = 0;
  BcpProbe positive;
  BcpProbe negative;
  int conflict_sides = 0;
  int64_t worst_irredundant = 0;
  int worst_active = 0;
  int64_t clause_imbalance = 0;
  int active_imbalance = 0;
  int minimum_fixed_gain = 0;
};

struct Selection {
  ProbeResult parent_probe;
  bool have_split = false;
  CandidateEvaluation chosen;
  int candidate_count = 0;
};

struct Node {
  long long id = 0;
  long long parent = -1;
  long long left = -1;
  long long right = -1;
  std::vector<int> cube;
  ProbeResult probe;
  int split_literal = 0;
  std::string split_source = "none";
  int candidate_count = 0;
  int selected_conflict_sides = -1;
  int64_t selected_worst_irredundant = -1;
  int selected_worst_active = -1;
  int64_t selected_clause_imbalance = -1;
  int selected_active_imbalance = -1;
  int selected_minimum_fixed_gain = -1;
};

class OccurrenceCollector : public CaDiCaL::ClauseIterator {
public:
  OccurrenceCollector(std::vector<int> &positive,
                      std::vector<int> &negative)
      : positive_(positive), negative_(negative) {}

  bool clause(const std::vector<int> &clause) override {
    for (int literal : clause) {
      if (literal > 0)
        ++positive_.at(static_cast<size_t>(literal));
      else
        ++negative_.at(static_cast<size_t>(-literal));
    }
    return true;
  }

private:
  std::vector<int> &positive_;
  std::vector<int> &negative_;
};

std::string json_escape(const std::string &input) {
  std::ostringstream output;
  for (unsigned char ch : input) {
    switch (ch) {
    case '\\':
      output << "\\\\";
      break;
    case '"':
      output << "\\\"";
      break;
    case '\n':
      output << "\\n";
      break;
    case '\r':
      output << "\\r";
      break;
    case '\t':
      output << "\\t";
      break;
    default:
      if (ch < 0x20)
        output << "\\u" << std::hex << std::setw(4) << std::setfill('0')
               << static_cast<int>(ch) << std::dec << std::setfill(' ');
      else
        output << ch;
    }
  }
  return output.str();
}

Dimacs read_dimacs_text(const std::string &path) {
  std::ifstream input(path);
  if (!input)
    throw std::runtime_error("cannot open input CNF: " + path);

  Dimacs result;
  std::string line;
  bool found_header = false;
  while (std::getline(input, line)) {
    result.lines.push_back(line);
    const size_t first = line.find_first_not_of(" \t\r");
    if (!found_header && first != std::string::npos &&
        line.compare(first, 6, "p cnf ") == 0) {
      std::istringstream header(line.substr(first));
      std::string p, cnf;
      if (!(header >> p >> cnf >> result.variables >> result.clauses) ||
          p != "p" || cnf != "cnf" || result.variables <= 0 ||
          result.clauses < 0)
        throw std::runtime_error("malformed DIMACS header");
      found_header = true;
    }
  }
  if (!found_header)
    throw std::runtime_error("missing DIMACS header");

  long long observed_clauses = 0;
  for (const std::string &raw : result.lines) {
    const size_t first = raw.find_first_not_of(" \t\r");
    if (first == std::string::npos || raw[first] == 'c' || raw[first] == 'p')
      continue;
    std::istringstream tokens(raw.substr(first));
    long long token = 0;
    while (tokens >> token) {
      if (!token) {
        ++observed_clauses;
        continue;
      }
      if (token == std::numeric_limits<int>::min() ||
          std::llabs(token) > result.variables)
        throw std::runtime_error("DIMACS literal outside declared range");
    }
  }
  if (observed_clauses != result.clauses)
    throw std::runtime_error("DIMACS clause-count mismatch");
  return result;
}

bool contains_variable(const std::vector<int> &cube, int variable) {
  for (int literal : cube)
    if (std::abs(literal) == variable)
      return true;
  return false;
}

void configure_solver(CaDiCaL::Solver &solver) {
  if (!solver.set("quiet", 1) || !solver.set("seed", 0))
    throw std::runtime_error("failed to configure frozen CaDiCaL options");
}

void load_formula(CaDiCaL::Solver &solver, const std::string &input_path,
                  const Dimacs &dimacs, const std::vector<int> &cube) {
  configure_solver(solver);
  int parsed_variables = 0;
  const char *error =
      solver.read_dimacs(input_path.c_str(), parsed_variables, 1);
  if (error)
    throw std::runtime_error(std::string("CaDiCaL parse error: ") + error);
  if (parsed_variables != dimacs.variables)
    throw std::runtime_error("CaDiCaL/parser variable-count mismatch");
  for (int variable = 1; variable <= dimacs.variables; ++variable)
    solver.freeze(variable);
  for (int literal : cube) {
    solver.add(literal);
    solver.add(0);
  }
}

int count_fixed(CaDiCaL::Solver &solver, int variables,
                std::vector<signed char> *values) {
  int count = 0;
  if (values)
    values->assign(static_cast<size_t>(variables) + 1, 0);
  for (int variable = 1; variable <= variables; ++variable) {
    const int value = solver.fixed(variable);
    if (!value)
      continue;
    ++count;
    if (values)
      values->at(static_cast<size_t>(variable)) = value > 0 ? 1 : -1;
  }
  return count;
}

ProbeResult probe_cube(const std::string &input_path, const Dimacs &dimacs,
                       const std::vector<int> &cube,
                       bool collect_candidate_state) {
  const auto started = Clock::now();
  ProbeResult result;
  CaDiCaL::Solver solver;
  load_formula(solver, input_path, dimacs, cube);

  const int bcp_status = solver.simplify(0);
  if (bcp_status == 20 || solver.inconsistent()) {
    result.terminal = TerminalKind::BCP_UNSAT;
  } else if (bcp_status == 10) {
    result.terminal = TerminalKind::SATISFIED;
  } else {
    result.bcp_fixed = count_fixed(solver, dimacs.variables, nullptr);
    result.suggested_split = solver.lookahead();
    if (solver.inconsistent()) {
      result.terminal = TerminalKind::LOOKAHEAD_UNSAT;
      result.suggested_split = 0;
    } else {
      result.fixed = count_fixed(
          solver, dimacs.variables,
          collect_candidate_state ? &result.fixed_values : nullptr);
      result.active = solver.active();
      result.irredundant = solver.irredundant();
      if (result.suggested_split) {
        const int variable = std::abs(result.suggested_split);
        if (variable > dimacs.variables || contains_variable(cube, variable) ||
            solver.fixed(variable))
          result.suggested_split = 0;
      }
      if (collect_candidate_state) {
        result.positive_occurrences.assign(
            static_cast<size_t>(dimacs.variables) + 1, 0);
        result.negative_occurrences.assign(
            static_cast<size_t>(dimacs.variables) + 1, 0);
        OccurrenceCollector collector(result.positive_occurrences,
                                      result.negative_occurrences);
        if (!solver.traverse_clauses(collector))
          throw std::runtime_error("remaining-clause traversal aborted");
      }
    }
  }

  result.probe_microseconds =
      std::chrono::duration_cast<std::chrono::microseconds>(Clock::now() -
                                                            started)
          .count();
  return result;
}

BcpProbe probe_bcp(const std::string &input_path, const Dimacs &dimacs,
                   const std::vector<int> &cube) {
  BcpProbe result;
  CaDiCaL::Solver solver;
  load_formula(solver, input_path, dimacs, cube);
  const int status = solver.simplify(0);
  result.conflict = status == 20 || solver.inconsistent();
  result.satisfied = status == 10;
  if (!result.conflict) {
    result.fixed = count_fixed(solver, dimacs.variables, nullptr);
    result.active = solver.active();
    result.irredundant = solver.irredundant();
  }
  return result;
}

void score_candidate(CandidateEvaluation &candidate, int base_bcp_fixed) {
  candidate.conflict_sides = static_cast<int>(candidate.positive.conflict) +
                             static_cast<int>(candidate.negative.conflict);
  const int64_t positive_clauses =
      candidate.positive.conflict ? 0 : candidate.positive.irredundant;
  const int64_t negative_clauses =
      candidate.negative.conflict ? 0 : candidate.negative.irredundant;
  const int positive_active =
      candidate.positive.conflict ? 0 : candidate.positive.active;
  const int negative_active =
      candidate.negative.conflict ? 0 : candidate.negative.active;
  candidate.worst_irredundant =
      std::max(positive_clauses, negative_clauses);
  candidate.worst_active = std::max(positive_active, negative_active);
  candidate.clause_imbalance =
      std::llabs(positive_clauses - negative_clauses);
  candidate.active_imbalance = std::abs(positive_active - negative_active);
  const int positive_gain = candidate.positive.conflict
                                ? std::numeric_limits<int>::max() / 4
                                : candidate.positive.fixed - base_bcp_fixed;
  const int negative_gain = candidate.negative.conflict
                                ? std::numeric_limits<int>::max() / 4
                                : candidate.negative.fixed - base_bcp_fixed;
  candidate.minimum_fixed_gain = std::min(positive_gain, negative_gain);
}

bool better_candidate(const CandidateEvaluation &left,
                      const CandidateEvaluation &right) {
  if (left.conflict_sides != right.conflict_sides)
    return left.conflict_sides < right.conflict_sides;
  if (left.worst_irredundant != right.worst_irredundant)
    return left.worst_irredundant < right.worst_irredundant;
  if (left.worst_active != right.worst_active)
    return left.worst_active < right.worst_active;
  if (left.clause_imbalance != right.clause_imbalance)
    return left.clause_imbalance < right.clause_imbalance;
  if (left.active_imbalance != right.active_imbalance)
    return left.active_imbalance < right.active_imbalance;
  if (left.minimum_fixed_gain != right.minimum_fixed_gain)
    return left.minimum_fixed_gain > right.minimum_fixed_gain;
  if (left.is_lookahead_variable != right.is_lookahead_variable)
    return left.is_lookahead_variable;
  if (left.is_physical_variable != right.is_physical_variable)
    return left.is_physical_variable;
  if (left.occurrence_balance != right.occurrence_balance)
    return left.occurrence_balance > right.occurrence_balance;
  if (left.occurrence_total != right.occurrence_total)
    return left.occurrence_total > right.occurrence_total;
  return left.variable < right.variable;
}

Selection select_split(const std::string &input_path, const Dimacs &dimacs,
                       const Node &node, int max_candidates) {
  Selection selection;
  selection.parent_probe = probe_cube(input_path, dimacs, node.cube, true);
  if (!selection.parent_probe.live())
    return selection;

  struct RankedVariable {
    int variable = 0;
    int occurrence_balance = 0;
    int occurrence_total = 0;
  };
  std::vector<RankedVariable> ranked;
  for (int variable = 1; variable <= dimacs.variables; ++variable) {
    if (contains_variable(node.cube, variable) ||
        selection.parent_probe.fixed_values.at(
            static_cast<size_t>(variable)))
      continue;
    const int positive = selection.parent_probe.positive_occurrences.at(
        static_cast<size_t>(variable));
    const int negative = selection.parent_probe.negative_occurrences.at(
        static_cast<size_t>(variable));
    if (!positive && !negative)
      continue;
    ranked.push_back(
        {variable, std::min(positive, negative), positive + negative});
  }
  std::sort(ranked.begin(), ranked.end(),
            [](const RankedVariable &left, const RankedVariable &right) {
              if (left.occurrence_balance != right.occurrence_balance)
                return left.occurrence_balance > right.occurrence_balance;
              if (left.occurrence_total != right.occurrence_total)
                return left.occurrence_total > right.occurrence_total;
              return left.variable < right.variable;
            });

  std::vector<RankedVariable> candidates;
  const int suggested_variable =
      std::abs(selection.parent_probe.suggested_split);
  if (suggested_variable) {
    const int positive = selection.parent_probe.positive_occurrences.at(
        static_cast<size_t>(suggested_variable));
    const int negative = selection.parent_probe.negative_occurrences.at(
        static_cast<size_t>(suggested_variable));
    candidates.push_back({suggested_variable, std::min(positive, negative),
                          positive + negative});
  }
  for (const RankedVariable &candidate : ranked) {
    if (static_cast<int>(candidates.size()) >= max_candidates)
      break;
    if (candidate.variable == suggested_variable)
      continue;
    candidates.push_back(candidate);
  }
  selection.candidate_count = static_cast<int>(candidates.size());
  if (candidates.empty()) {
    selection.parent_probe.terminal = TerminalKind::NO_SPLIT;
    return selection;
  }

  bool have_best = false;
  for (const RankedVariable &ranked_candidate : candidates) {
    CandidateEvaluation evaluation;
    evaluation.variable = ranked_candidate.variable;
    evaluation.is_lookahead_variable =
        ranked_candidate.variable == suggested_variable;
    evaluation.is_physical_variable = ranked_candidate.variable <= 400;
    evaluation.occurrence_balance = ranked_candidate.occurrence_balance;
    evaluation.occurrence_total = ranked_candidate.occurrence_total;

    std::vector<int> branch = node.cube;
    branch.push_back(evaluation.variable);
    evaluation.positive = probe_bcp(input_path, dimacs, branch);
    branch.back() = -evaluation.variable;
    evaluation.negative = probe_bcp(input_path, dimacs, branch);
    score_candidate(evaluation, selection.parent_probe.bcp_fixed);

    if (!have_best || better_candidate(evaluation, selection.chosen)) {
      selection.chosen = std::move(evaluation);
      have_best = true;
    }
  }
  selection.have_split = have_best;
  return selection;
}

bool harder_leaf(const Node &left, const Node &right) {
  if (left.probe.irredundant != right.probe.irredundant)
    return left.probe.irredundant > right.probe.irredundant;
  if (left.probe.active != right.probe.active)
    return left.probe.active > right.probe.active;
  if (left.cube.size() != right.cube.size())
    return left.cube.size() < right.cube.size();
  return left.id < right.id;
}

long long choose_hardest_leaf(const std::vector<Node> &nodes,
                              const std::vector<long long> &frontier) {
  long long best = -1;
  for (long long id : frontier) {
    const Node &node = nodes.at(static_cast<size_t>(id));
    if (!node.probe.live())
      continue;
    if (best < 0 || harder_leaf(node, nodes.at(static_cast<size_t>(best))))
      best = id;
  }
  return best;
}

void validate_cube(const std::vector<int> &cube, int variables) {
  std::set<int> seen;
  for (int literal : cube) {
    const int variable = std::abs(literal);
    if (!variable || variable > variables)
      throw std::runtime_error("cube literal outside DIMACS variable range");
    if (!seen.insert(variable).second)
      throw std::runtime_error("cube repeats a variable");
  }
}

bool cubes_conflict(const std::vector<int> &left,
                    const std::vector<int> &right) {
  for (int first : left)
    for (int second : right)
      if (first == -second)
        return true;
  return false;
}

void validate_adaptive_cover(const std::vector<Node> &nodes,
                             const std::vector<long long> &frontier,
                             int variables) {
  if (nodes.empty() || nodes[0].id != 0 || nodes[0].parent != -1 ||
      !nodes[0].cube.empty())
    throw std::runtime_error("invalid root node");
  std::set<long long> leaf_ids(frontier.begin(), frontier.end());
  if (leaf_ids.size() != frontier.size())
    throw std::runtime_error("frontier contains duplicate nodes");

  for (const Node &node : nodes) {
    validate_cube(node.cube, variables);
    const bool is_leaf = node.left < 0 && node.right < 0;
    if (is_leaf != (leaf_ids.count(node.id) != 0))
      throw std::runtime_error("frontier/tree leaf mismatch");
    if (is_leaf)
      continue;
    if (node.left < 0 || node.right < 0 || !node.split_literal)
      throw std::runtime_error("internal node lacks complementary children");
    const Node &left = nodes.at(static_cast<size_t>(node.left));
    const Node &right = nodes.at(static_cast<size_t>(node.right));
    if (left.parent != node.id || right.parent != node.id)
      throw std::runtime_error("child parent id mismatch");
    std::vector<int> expected = node.cube;
    expected.push_back(node.split_literal);
    if (left.cube != expected)
      throw std::runtime_error("positive child cube mismatch");
    expected.back() = -node.split_literal;
    if (right.cube != expected)
      throw std::runtime_error("negative child cube mismatch");
  }

  for (size_t i = 0; i < frontier.size(); ++i)
    for (size_t j = i + 1; j < frontier.size(); ++j)
      if (!cubes_conflict(nodes.at(static_cast<size_t>(frontier[i])).cube,
                          nodes.at(static_cast<size_t>(frontier[j])).cube))
        throw std::runtime_error("adaptive cubes are not pairwise exclusive");
}

std::vector<long long> ordered_frontier(std::vector<long long> frontier) {
  std::sort(frontier.begin(), frontier.end());
  return frontier;
}

void write_cubes(const std::string &path, const std::vector<Node> &nodes,
                 const std::vector<long long> &frontier) {
  std::ofstream output(path);
  if (!output)
    throw std::runtime_error("cannot create cubes file: " + path);
  for (long long id : ordered_frontier(frontier)) {
    output << 'a';
    for (int literal : nodes.at(static_cast<size_t>(id)).cube)
      output << ' ' << literal;
    output << " 0\n";
  }
}

void write_icnf(const std::string &path, const Dimacs &dimacs,
                const std::vector<Node> &nodes,
                const std::vector<long long> &frontier) {
  std::ofstream output(path);
  if (!output)
    throw std::runtime_error("cannot create INCCNF file: " + path);
  bool replaced_header = false;
  for (const std::string &line : dimacs.lines) {
    const size_t first = line.find_first_not_of(" \t\r");
    if (!replaced_header && first != std::string::npos &&
        line.compare(first, 6, "p cnf ") == 0) {
      output << "p inccnf\n";
      replaced_header = true;
    } else {
      output << line << '\n';
    }
  }
  for (long long id : ordered_frontier(frontier)) {
    output << 'a';
    for (int literal : nodes.at(static_cast<size_t>(id)).cube)
      output << ' ' << literal;
    output << " 0\n";
  }
}

void write_leaf_cnfs(const std::string &prefix, const Dimacs &dimacs,
                     const std::vector<Node> &nodes,
                     const std::vector<long long> &frontier) {
  const std::vector<long long> ordered = ordered_frontier(frontier);
  for (size_t index = 0; index < ordered.size(); ++index) {
    const Node &node = nodes.at(static_cast<size_t>(ordered[index]));
    std::ostringstream path;
    path << prefix << "-leaf-" << std::setw(4) << std::setfill('0') << index
         << ".cnf";
    std::ofstream output(path.str());
    if (!output)
      throw std::runtime_error("cannot create leaf CNF: " + path.str());
    bool replaced_header = false;
    for (const std::string &line : dimacs.lines) {
      const size_t first = line.find_first_not_of(" \t\r");
      if (!replaced_header && first != std::string::npos &&
          line.compare(first, 6, "p cnf ") == 0) {
        output << "p cnf " << dimacs.variables << ' '
               << dimacs.clauses + static_cast<long long>(node.cube.size())
               << "\n";
        replaced_header = true;
      } else {
        output << line << '\n';
      }
    }
    for (int literal : node.cube)
      output << literal << " 0\n";
  }
}

void write_tree(const std::string &path, const std::vector<Node> &nodes) {
  std::ofstream output(path);
  if (!output)
    throw std::runtime_error("cannot create tree record: " + path);
  output << "node_id\tparent_id\tdepth\tterminal\tbcp_fixed\tfixed\t"
            "active\tirredundant\tprobe_us\tsplit_literal\tsplit_source\t"
            "candidate_count\tconflict_sides\tworst_irredundant\t"
            "worst_active\tclause_imbalance\tactive_imbalance\t"
            "minimum_fixed_gain\tleft\tright\tcube\n";
  for (const Node &node : nodes) {
    output << node.id << '\t' << node.parent << '\t' << node.cube.size()
           << '\t' << terminal_name(node.probe.terminal) << '\t'
           << node.probe.bcp_fixed << '\t' << node.probe.fixed << '\t'
           << node.probe.active << '\t' << node.probe.irredundant << '\t'
           << node.probe.probe_microseconds << '\t' << node.split_literal
           << '\t' << node.split_source << '\t' << node.candidate_count
           << '\t' << node.selected_conflict_sides << '\t'
           << node.selected_worst_irredundant << '\t'
           << node.selected_worst_active << '\t'
           << node.selected_clause_imbalance << '\t'
           << node.selected_active_imbalance << '\t'
           << node.selected_minimum_fixed_gain << '\t' << node.left << '\t'
           << node.right << '\t';
    for (int literal : node.cube)
      output << literal << ' ';
    output << "0\n";
  }
}

void write_leaf_manifest(const std::string &path,
                         const std::vector<Node> &nodes,
                         const std::vector<long long> &frontier) {
  std::ofstream output(path);
  if (!output)
    throw std::runtime_error("cannot create leaf manifest: " + path);
  output << "index\tnode_id\tdepth\tterminal\tbcp_fixed\tfixed\tactive\t"
            "irredundant\tprobe_us\tcube\n";
  const std::vector<long long> ordered = ordered_frontier(frontier);
  for (size_t index = 0; index < ordered.size(); ++index) {
    const Node &node = nodes.at(static_cast<size_t>(ordered[index]));
    output << index << '\t' << node.id << '\t' << node.cube.size() << '\t'
           << terminal_name(node.probe.terminal) << '\t'
           << node.probe.bcp_fixed << '\t' << node.probe.fixed << '\t'
           << node.probe.active << '\t' << node.probe.irredundant << '\t'
           << node.probe.probe_microseconds << '\t';
    for (int literal : node.cube)
      output << literal << ' ';
    output << "0\n";
  }
}

void write_coverage(const std::string &path, const std::string &input_path,
                    const Dimacs &dimacs, int target_leaves,
                    int max_candidates, const std::vector<Node> &nodes,
                    const std::vector<long long> &frontier) {
  int bcp_unsat = 0;
  int lookahead_unsat = 0;
  int satisfied = 0;
  int no_split = 0;
  int live = 0;
  size_t min_depth = std::numeric_limits<size_t>::max();
  size_t max_depth = 0;
  for (long long id : frontier) {
    const Node &node = nodes.at(static_cast<size_t>(id));
    min_depth = std::min(min_depth, node.cube.size());
    max_depth = std::max(max_depth, node.cube.size());
    switch (node.probe.terminal) {
    case TerminalKind::BCP_UNSAT:
      ++bcp_unsat;
      break;
    case TerminalKind::LOOKAHEAD_UNSAT:
      ++lookahead_unsat;
      break;
    case TerminalKind::SATISFIED:
      ++satisfied;
      break;
    case TerminalKind::NO_SPLIT:
      ++no_split;
      break;
    case TerminalKind::NONE:
      ++live;
      break;
    }
  }

  std::ofstream output(path);
  if (!output)
    throw std::runtime_error("cannot create coverage record: " + path);
  output << "{\n"
         << "  \"schema_version\": 1,\n"
         << "  \"authority\": \"TEST_ONLY\",\n"
         << "  \"algorithm\": \"adaptive-best-first-bcp-lookahead-v1\",\n"
         << "  \"input_cnf\": \"" << json_escape(input_path) << "\",\n"
         << "  \"input_variables\": " << dimacs.variables << ",\n"
         << "  \"input_clauses\": " << dimacs.clauses << ",\n"
         << "  \"target_leaf_count\": " << target_leaves << ",\n"
         << "  \"observed_leaf_count\": " << frontier.size() << ",\n"
         << "  \"target_reached\": "
         << (static_cast<int>(frontier.size()) == target_leaves ? "true"
                                                               : "false")
         << ",\n"
         << "  \"internal_node_count\": " << nodes.size() - frontier.size()
         << ",\n"
         << "  \"minimum_leaf_depth\": "
         << (frontier.empty() ? 0 : min_depth) << ",\n"
         << "  \"maximum_leaf_depth\": " << max_depth << ",\n"
         << "  \"candidate_limit_per_split\": " << max_candidates << ",\n"
         << "  \"bcp_unsat_leaves\": " << bcp_unsat << ",\n"
         << "  \"lookahead_unsat_leaves\": " << lookahead_unsat << ",\n"
         << "  \"satisfied_leaves\": " << satisfied << ",\n"
         << "  \"no_split_leaves\": " << no_split << ",\n"
         << "  \"live_leaves\": " << live << ",\n"
         << "  \"adaptive_tree_validated\": true,\n"
         << "  \"pairwise_mutually_exclusive_validated\": true,\n"
         << "  \"exhaustive_by_complementary_branch_induction\": true,\n"
         << "  \"terminal_classification_is_proof\": false,\n"
         << "  \"scientific_terminal\": false\n"
         << "}\n";
}

int parse_positive_int(const char *text, const char *name, int maximum) {
  char *end = nullptr;
  const long value = std::strtol(text, &end, 10);
  if (!text[0] || !end || *end || value < 1 || value > maximum)
    throw std::runtime_error(std::string(name) + " must be in 1.." +
                             std::to_string(maximum));
  return static_cast<int>(value);
}

} // namespace

int main(int argc, char **argv) {
  try {
    if (argc < 4 || argc > 5) {
      std::cerr << "usage: " << argv[0]
                << " INPUT.cnf TARGET_LEAVES OUTPUT_PREFIX "
                   "[MAX_CANDIDATES=32]\n";
      return 64;
    }
    const std::string input_path = argv[1];
    const int target_leaves =
        parse_positive_int(argv[2], "TARGET_LEAVES", 4096);
    const std::string prefix = argv[3];
    const int max_candidates =
        argc == 5 ? parse_positive_int(argv[4], "MAX_CANDIDATES", 1024) : 32;
    const Dimacs dimacs = read_dimacs_text(input_path);

    std::vector<Node> nodes(1);
    nodes[0].id = 0;
    nodes[0].probe = probe_cube(input_path, dimacs, nodes[0].cube, false);
    std::vector<long long> frontier{0};

    while (static_cast<int>(frontier.size()) < target_leaves) {
      const long long selected_id = choose_hardest_leaf(nodes, frontier);
      if (selected_id < 0)
        break;
      Selection selection = select_split(
          input_path, dimacs, nodes.at(static_cast<size_t>(selected_id)),
          max_candidates);
      Node &selected = nodes.at(static_cast<size_t>(selected_id));
      selected.probe = selection.parent_probe;
      if (!selection.have_split)
        continue;

      selected.split_literal = selection.chosen.variable;
      selected.split_source = selection.chosen.is_lookahead_variable
                                  ? "lookahead-scored"
                                  : "bcp-balanced";
      selected.candidate_count = selection.candidate_count;
      selected.selected_conflict_sides = selection.chosen.conflict_sides;
      selected.selected_worst_irredundant =
          selection.chosen.worst_irredundant;
      selected.selected_worst_active = selection.chosen.worst_active;
      selected.selected_clause_imbalance =
          selection.chosen.clause_imbalance;
      selected.selected_active_imbalance =
          selection.chosen.active_imbalance;
      selected.selected_minimum_fixed_gain =
          selection.chosen.minimum_fixed_gain;

      const int split_literal = selected.split_literal;
      const std::vector<int> parent_cube = selected.cube;
      const long long positive_id = static_cast<long long>(nodes.size());
      const long long negative_id = positive_id + 1;
      selected.left = positive_id;
      selected.right = negative_id;

      Node positive;
      positive.id = positive_id;
      positive.parent = selected_id;
      positive.cube = parent_cube;
      positive.cube.push_back(split_literal);
      positive.probe =
          probe_cube(input_path, dimacs, positive.cube, false);

      Node negative;
      negative.id = negative_id;
      negative.parent = selected_id;
      negative.cube = parent_cube;
      negative.cube.push_back(-split_literal);
      negative.probe =
          probe_cube(input_path, dimacs, negative.cube, false);

      nodes.push_back(std::move(positive));
      nodes.push_back(std::move(negative));

      const auto position =
          std::find(frontier.begin(), frontier.end(), selected_id);
      if (position == frontier.end())
        throw std::runtime_error("selected leaf missing from frontier");
      *position = positive_id;
      frontier.push_back(negative_id);
    }

    validate_adaptive_cover(nodes, frontier, dimacs.variables);
    write_cubes(prefix + ".cubes", nodes, frontier);
    write_icnf(prefix + ".icnf", dimacs, nodes, frontier);
    write_leaf_cnfs(prefix, dimacs, nodes, frontier);
    write_tree(prefix + "-tree.tsv", nodes);
    write_leaf_manifest(prefix + "-leaves.tsv", nodes, frontier);
    write_coverage(prefix + "-coverage.json", input_path, dimacs,
                   target_leaves, max_candidates, nodes, frontier);

    int live = 0;
    int terminal = 0;
    size_t maximum_depth = 0;
    for (long long id : frontier) {
      const Node &node = nodes.at(static_cast<size_t>(id));
      if (node.probe.live())
        ++live;
      else
        ++terminal;
      maximum_depth = std::max(maximum_depth, node.cube.size());
    }
    std::cout << "c algorithm adaptive-best-first-bcp-lookahead-v1\n"
              << "c input_variables " << dimacs.variables << "\n"
              << "c input_clauses " << dimacs.clauses << "\n"
              << "c target_leaf_count " << target_leaves << "\n"
              << "c observed_leaf_count " << frontier.size() << "\n"
              << "c live_leaf_count " << live << "\n"
              << "c terminal_leaf_count " << terminal << "\n"
              << "c maximum_leaf_depth " << maximum_depth << "\n"
              << "c target_reached "
              << (static_cast<int>(frontier.size()) == target_leaves ? 1 : 0)
              << "\n";
    return 0;
  } catch (const std::exception &error) {
    std::cerr << "error: " << error.what() << "\n";
    return 1;
  }
}
