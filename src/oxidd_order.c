#define _POSIX_C_SOURCE 200809L
#include "tlsf/oxidd_common.h"

#include <ctype.h>
#include <errno.h>
#include <stdlib.h>

#define ORDER_UNSEEN UINT32_MAX
#define FNV_OFFSET UINT64_C(1469598103934665603)
#define FNV_PRIME UINT64_C(1099511628211)

static uint64_t hash_bytes(uint64_t hash, const void *data, size_t size) {
  const unsigned char *bytes = data;
  for (size_t i = 0; i < size; i++) {
    hash ^= bytes[i];
    hash *= FNV_PRIME;
  }
  return hash;
}

static uint64_t hash_order(const oxidd_var_no_t *order, size_t count) {
  uint64_t hash = hash_bytes(FNV_OFFSET, &count, sizeof count);
  for (size_t i = 0; i < count; i++)
    hash = hash_bytes(hash, &order[i], sizeof order[i]);
  return hash;
}

const char *oxidd_var_order_name(OxiddVarOrder order) {
  switch (order) {
  case OXIDD_VAR_ORDER_INPUT_FIRST:
    return "input-first";
  case OXIDD_VAR_ORDER_STATE_FIRST:
    return "state-first";
  case OXIDD_VAR_ORDER_FANIN_DFS:
    return "fanin-dfs";
  }
  return "invalid";
}

bool oxidd_var_order_is_default(const OxiddSolveOptions *options) {
  return options->var_order == OXIDD_VAR_ORDER_INPUT_FIRST &&
         !options->order_file;
}

static bool fail(const OxiddSolveOptions *options, OxiddFailureKind kind,
                 const char *operation) {
  oxidd_record_failure(options, kind, "manager_create", operation, 0, 0);
  return false;
}

static bool parse_decimal_line(char *line, uint64_t *value) {
  char *start = line;
  while (isspace((unsigned char)*start))
    start++;
  if (!isdigit((unsigned char)*start))
    return false;
  errno = 0;
  char *end = nullptr;
  unsigned long long parsed = strtoull(start, &end, 10);
  if (errno || end == start)
    return false;
  while (isspace((unsigned char)*end))
    end++;
  if (*end)
    return false;
  *value = parsed;
  return true;
}

static bool parse_order_file(const OxiddSolveOptions *options, size_t count,
                             OxiddResolvedOrder *resolved) {
  FILE *input = fopen(options->order_file, "r");
  if (!input)
    return fail(options, OXIDD_FAILURE_CONFIGURATION, "order_file_open");
  char *line = nullptr;
  size_t line_cap = 0;
  ssize_t length = getline(&line, &line_cap, input);
  uint64_t file_hash = FNV_OFFSET;
  if (length >= 0)
    file_hash = hash_bytes(file_hash, line, (size_t)length);
  char tag[64], extra;
  unsigned long long declared = 0;
  bool ok = length >= 0 &&
            sscanf(line, "%63s %llu %c", tag, &declared, &extra) == 2 &&
            strcmp(tag, "tlsfsolve-order-v1") == 0 && declared == count;
  bool *seen = count ? calloc(count, sizeof *seen) : nullptr;
  if (count && !seen)
    ok = false;
  for (size_t i = 0; i < count && ok; i++) {
    length = getline(&line, &line_cap, input);
    if (length < 0) {
      ok = false;
      break;
    }
    file_hash = hash_bytes(file_hash, line, (size_t)length);
    uint64_t value;
    if (!parse_decimal_line(line, &value) || value >= count || seen[value]) {
      ok = false;
      break;
    }
    seen[value] = true;
    resolved->local[i] = (oxidd_var_no_t)value;
  }
  while (ok && (length = getline(&line, &line_cap, input)) >= 0) {
    file_hash = hash_bytes(file_hash, line, (size_t)length);
    for (ssize_t i = 0; i < length; i++)
      if (!isspace((unsigned char)line[i])) {
        ok = false;
        break;
      }
  }
  bool io_error = ferror(input) != 0;
  free(seen);
  free(line);
  fclose(input);
  if (!ok || io_error)
    return fail(options, OXIDD_FAILURE_CONFIGURATION, "order_file_invalid");
  resolved->name = "custom";
  resolved->file_hash = file_hash;
  return true;
}

static uint32_t max_aig_var(const Aig *game) {
  uint32_t maxvar = 0;
  for (uint32_t i = 0; i < aig_num_inputs(game); i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < aig_num_latches(game); i++) {
    uint32_t cur;
    aig_latch_at(game, i, &cur, nullptr, nullptr);
    if (cur / 2 > maxvar)
      maxvar = cur / 2;
  }
  for (uint32_t i = 0; i < aig_num_ands(game); i++) {
    uint32_t lhs;
    aig_and_at(game, i, &lhs, nullptr, nullptr);
    if (lhs / 2 > maxvar)
      maxvar = lhs / 2;
  }
  return maxvar;
}

static bool collect_roots(const Aig *game, const OxiddSolveOptions *options,
                          uint32_t **roots_out, size_t *count_out) {
  bool typed = options->safety_objective == OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  uint32_t objectives = typed ? aig_num_bad(game) : 1;
  size_t count = (size_t)objectives + aig_num_latches(game) +
                 aig_num_justice(game) + aig_num_fairness(game);
  uint32_t *roots = count ? calloc(count, sizeof *roots) : nullptr;
  if (count && !roots)
    return false;
  size_t k = 0;
  for (uint32_t i = 0; i < objectives; i++) {
    if (typed)
      aig_bad_at(game, i, &roots[k++]);
    else if (options->safety_output_index < aig_num_outputs(game))
      aig_output_at(game, options->safety_output_index, &roots[k++]);
    else {
      free(roots);
      return false;
    }
  }
  for (uint32_t i = 0; i < aig_num_latches(game); i++)
    aig_latch_at(game, i, nullptr, &roots[k++], nullptr);
  for (uint32_t i = 0; i < aig_num_justice(game); i++) {
    const uint32_t *lits = nullptr;
    uint32_t n = 0;
    aig_justice_at(game, i, &lits, &n);
    if (n != 1) {
      free(roots);
      return false;
    }
    roots[k++] = lits[0];
  }
  for (uint32_t i = 0; i < aig_num_fairness(game); i++)
    roots[k++] = aig_fairness_at(game, i);
  *roots_out = roots;
  *count_out = count;
  return true;
}

static bool fanin_dfs_order(const Aig *game, const OxiddSolveOptions *options,
                            uint32_t auxiliary_vars,
                            OxiddResolvedOrder *resolved) {
  uint32_t ni = aig_num_inputs(game), nl = aig_num_latches(game);
  uint32_t maxvar = max_aig_var(game);
  uint32_t *local = malloc(((size_t)maxvar + 1) * sizeof *local);
  uint32_t *left = calloc((size_t)maxvar + 1, sizeof *left);
  uint32_t *right = calloc((size_t)maxvar + 1, sizeof *right);
  bool *is_and = calloc((size_t)maxvar + 1, sizeof *is_and);
  bool *visited = calloc((size_t)maxvar + 1, sizeof *visited);
  bool *ordered =
      resolved->count ? calloc(resolved->count, sizeof *ordered) : nullptr;
  uint32_t *roots = nullptr;
  size_t root_count = 0;
  size_t stack_cap = (size_t)aig_num_ands(game) * 2 + 1;
  uint32_t *stack = malloc(stack_cap * sizeof *stack);
  bool ok = local && left && right && is_and && visited && stack &&
            (!resolved->count || ordered) &&
            collect_roots(game, options, &roots, &root_count);
  (void)auxiliary_vars;
  if (!ok)
    goto done;
  for (uint32_t v = 0; v <= maxvar; v++)
    local[v] = ORDER_UNSEEN;
  for (uint32_t i = 0; i < ni; i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    local[lit / 2] = i;
  }
  for (uint32_t i = 0; i < nl; i++) {
    uint32_t lit;
    aig_latch_at(game, i, &lit, nullptr, nullptr);
    local[lit / 2] = ni + i;
  }
  for (uint32_t i = 0; i < aig_num_ands(game); i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(game, i, &lhs, &r0, &r1);
    uint32_t var = lhs / 2;
    left[var] = r0;
    right[var] = r1;
    is_and[var] = true;
  }
  size_t out = 0;
  for (size_t root = 0; root < root_count && ok; root++) {
    size_t top = 0;
    stack[top++] = roots[root];
    while (top && ok) {
      uint32_t lit = stack[--top], var = lit / 2;
      if (!var)
        continue;
      if (var > maxvar || visited[var]) {
        if (var > maxvar)
          ok = false;
        continue;
      }
      visited[var] = true;
      if (local[var] != ORDER_UNSEEN) {
        uint32_t identity = local[var];
        if (!ordered[identity]) {
          resolved->local[out++] = identity;
          ordered[identity] = true;
        }
      } else if (is_and[var]) {
        uint32_t first = left[var], second = right[var];
        if (second < first) {
          uint32_t tmp = first;
          first = second;
          second = tmp;
        }
        if (top + 2 > stack_cap)
          ok = false;
        else {
          stack[top++] = second;
          stack[top++] = first;
        }
      } else {
        ok = false;
      }
    }
  }
  for (uint32_t i = 0; i < ni + nl && ok; i++)
    if (!ordered[i]) {
      resolved->local[out++] = i;
      ordered[i] = true;
    }
  for (uint32_t i = ni + nl; i < resolved->count && ok; i++) {
    resolved->local[out++] = i;
    ordered[i] = true;
  }
  ok = ok && out == resolved->count;

done:
  free(stack);
  free(roots);
  free(ordered);
  free(visited);
  free(is_and);
  free(right);
  free(left);
  free(local);
  return ok;
}

bool oxidd_resolve_var_order(const Aig *game, const OxiddSolveOptions *options,
                             uint32_t auxiliary_vars,
                             OxiddResolvedOrder *resolved) {
  *resolved = (OxiddResolvedOrder){0};
  uint32_t ni = aig_num_inputs(game), nl = aig_num_latches(game);
  if (auxiliary_vars > UINT32_MAX - ni - nl)
    return fail(options, OXIDD_FAILURE_CONFIGURATION, "order_var_overflow");
  resolved->count = (size_t)ni + nl + auxiliary_vars;
  resolved->local = resolved->count
                        ? calloc(resolved->count, sizeof *resolved->local)
                        : nullptr;
  if (resolved->count && !resolved->local)
    return fail(options, OXIDD_FAILURE_HOST, "order_allocation");
  bool ok = true;
  if (options->order_file) {
    ok = parse_order_file(options, resolved->count, resolved);
  } else if (options->var_order == OXIDD_VAR_ORDER_INPUT_FIRST) {
    resolved->name = "input-first";
    for (size_t i = 0; i < resolved->count; i++)
      resolved->local[i] = (oxidd_var_no_t)i;
  } else if (options->var_order == OXIDD_VAR_ORDER_STATE_FIRST) {
    resolved->name = "state-first";
    size_t k = 0;
    for (uint32_t i = 0; i < nl; i++)
      resolved->local[k++] = ni + i;
    for (uint32_t i = 0; i < ni; i++)
      resolved->local[k++] = i;
    for (uint32_t i = ni + nl; i < resolved->count; i++)
      resolved->local[k++] = i;
  } else if (options->var_order == OXIDD_VAR_ORDER_FANIN_DFS) {
    resolved->name = "fanin-dfs";
    ok = fanin_dfs_order(game, options, auxiliary_vars, resolved);
    if (!ok)
      fail(options, OXIDD_FAILURE_HOST, "fanin_order_allocation_or_input");
  } else {
    ok = fail(options, OXIDD_FAILURE_CONFIGURATION, "order_invalid");
  }
  if (!ok) {
    oxidd_resolved_order_free(resolved);
    return false;
  }
  resolved->hash = hash_order(resolved->local, resolved->count);
  return true;
}

bool oxidd_apply_var_order(oxidd_bdd_manager_t manager, uint32_t var_base,
                           const OxiddSolveOptions *options,
                           const OxiddResolvedOrder *resolved) {
  oxidd_var_no_t *absolute =
      resolved->count ? malloc(resolved->count * sizeof *absolute) : nullptr;
  if (resolved->count && !absolute)
    return fail(options, OXIDD_FAILURE_HOST, "order_apply_allocation");
  bool ok = true;
  for (size_t i = 0; i < resolved->count; i++) {
    if (resolved->local[i] > UINT32_MAX - var_base) {
      ok = false;
      break;
    }
    absolute[i] = var_base + resolved->local[i];
  }
  if (ok && !oxidd_var_order_is_default(options))
    oxidd_bdd_manager_set_var_order(manager, absolute, resolved->count);
  for (size_t i = 0; i < resolved->count && ok; i++)
    ok =
        oxidd_bdd_manager_level_to_var(
            manager, (oxidd_level_no_t)(var_base + (uint32_t)i)) == absolute[i];
  if (!ok)
    fail(options, OXIDD_FAILURE_CONFIGURATION, "order_apply_mismatch");
#ifndef NDEBUG
  if (ok && options->verbosity) {
    size_t capacity = 32 + resolved->count * 12;
    char *list = malloc(capacity);
    if (list) {
      size_t used = 0;
      list[used++] = '[';
      for (size_t i = 0; i < resolved->count; i++)
        used += (size_t)snprintf(list + used, capacity - used, "%s%u",
                                 i ? "," : "", resolved->local[i]);
      list[used++] = ']';
      list[used] = '\0';
      oxidd_trace(options, "manager_create", "variable_order",
                  ",\"requested\":\"%s\",\"effective\":\"%s\","
                  "\"order_hash\":\"%016llx\","
                  "\"order_file_hash\":\"%016llx\",\"var_base\":%u,"
                  "\"order\":%s",
                  options->order_file
                      ? "custom"
                      : oxidd_var_order_name(options->var_order),
                  resolved->name, (unsigned long long)resolved->hash,
                  (unsigned long long)resolved->file_hash, var_base, list);
      free(list);
    }
  }
#endif
  free(absolute);
  return ok;
}

void oxidd_resolved_order_free(OxiddResolvedOrder *resolved) {
  free(resolved->local);
  *resolved = (OxiddResolvedOrder){0};
}
