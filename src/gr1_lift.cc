#include "tlsf/gr1_lift.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/oxidd_options.h"
#include "tlsf/templates.h"
#include "oxidd_common.h"
#include "pipeline_source_internal.h"

#include <boost/json.hpp>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
namespace j = boost::json;
using namespace oxidd::capi;
using J = j::value;
using O = j::object;
using A = j::array;
struct Failure : std::runtime_error {
  TlsfGr1LiftStatus status;
  std::string stage;
  Failure(TlsfGr1LiftStatus s, std::string at, std::string why)
      : std::runtime_error(why), status(s), stage(std::move(at)) {}
};
[[noreturn]] void decline(const char *stage, const char *why) {
  throw Failure(TLSF_GR1_LIFT_DECLINED, stage, why);
}
uint64_t now_ns() {
  timespec ts{};
  if (clock_gettime(CLOCK_MONOTONIC, &ts))
    throw Failure(TLSF_GR1_LIFT_ERROR, "clock", "CLOCK_MONOTONIC failed");
  return uint64_t(ts.tv_sec) * 1000000000ull + uint64_t(ts.tv_nsec);
}
struct Config {
  TlsfGr1LiftOptions o{};
  void check(const char *stage) const {
    if (o.cancelled && o.cancelled(o.cancel_ctx))
      throw Failure(TLSF_GR1_LIFT_CANCELLED, stage, "cancelled");
    if (o.deadline_mono_ns && now_ns() >= o.deadline_mono_ns)
      throw Failure(TLSF_GR1_LIFT_DEADLINE, stage, "deadline exceeded");
  }
  void bytes(size_t n, const char *stage) const {
    check(stage);
    if (n > o.max_artifact_bytes)
      throw Failure(TLSF_GR1_LIFT_LIMIT, stage, "artifact byte cap exceeded");
  }
};
std::string str(const J &v) { return std::string(v.as_string()); }
std::string s(const O &o, const char *k) { return str(o.at(k)); }
int64_t num(const J &v) { return v.is_int64() ? v.as_int64() : int64_t(v.as_uint64()); }
int64_t n(const O &o, const char *k) { return num(o.at(k)); }
std::string dump(const J &v) { return j::serialize(v); }
std::vector<int> ints(const A &a) {
  std::vector<int> x;
  for (const auto &v : a) x.push_back(int(num(v)));
  return x;
}
std::string join(const std::vector<std::string> &v) {
  std::string x;
  for (const auto &part : v) { x += std::to_string(part.size()) + ":" + part; }
  return x;
}
template <typename T> std::string field(const T &v) { return std::to_string(v); }
std::string key(std::initializer_list<std::string> parts) {
  return join(std::vector<std::string>(parts));
}

struct Instance {
  TlsfGr1Reduction r{};
  O data;
  std::map<std::string, int64_t> overrides;
  std::vector<int> members;
  std::string cert_aag, cert_json;
  std::unique_ptr<Aig, decltype(&aig_free)> cert{nullptr, &aig_free};
  O cert_meta;
  ~Instance() { tlsf_gr1_reduction_clear(&r); }
  Instance() = default;
  Instance(const Instance &) = delete;
};

std::unique_ptr<Aig, decltype(&aig_free)> parse_aig(const char *bytes, size_t size) {
  FILE *fp = fmemopen(const_cast<char *>(bytes), size, "r");
  if (!fp) throw Failure(TLSF_GR1_LIFT_ERROR, "aag", "cannot open memory stream");
  Aig *raw = aig_read_aag(fp);
  fclose(fp);
  if (!raw) decline("aag", "invalid AAG artifact");
  return {raw, &aig_free};
}
std::string render_aig(const Aig *game, const Config &cfg) {
  char *bytes = nullptr;
  size_t size = 0;
  FILE *fp = open_memstream(&bytes, &size);
  if (!fp) throw Failure(TLSF_GR1_LIFT_ERROR, "aag", "cannot allocate memory stream");
  aig_write_aag(fp, game);
  if (fclose(fp)) { free(bytes); throw Failure(TLSF_GR1_LIFT_ERROR, "aag", "write failed"); }
  std::string out(bytes, size);
  free(bytes);
  cfg.bytes(out.size(), "aag");
  return out;
}

std::unique_ptr<Instance> lower(const uint8_t *source, size_t size,
                                const std::map<std::string, int64_t> &overrides,
                                TlsfGr1ReductionSemantics semantics,
                                const Config &cfg) {
  cfg.check("expand");
  auto instance = std::make_unique<Instance>();
  instance->overrides = overrides;
  std::vector<ParamOverride> params;
  params.reserve(overrides.size());
  for (const auto &[name, value] : overrides)
    params.push_back({name.c_str(), value});
  TlsfPipelineError perr{};
  TlsfPipelineOptions popts{};
  popts.certify = true;
  popts.template_mask = TPL_ALL;
  popts.overrides = params.data();
  popts.n_overrides = params.size();
  popts.require_unambiguous_origin = true;
  popts.error = &perr;
  auto pipeline = std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)>(
      tlsf_pipeline_load_bytes(source, size, &popts), &tlsf_pipeline_free);
  if (!pipeline) {
    if (perr.status == TLSF_PIPELINE_LIMIT)
      throw Failure(TLSF_GR1_LIFT_LIMIT, "expand", perr.message);
    decline("expand", perr.message[0] ? perr.message : "source expansion failed");
  }
  cfg.check("reduce");
  TlsfGr1ReductionOptions ro{};
  ro.semantics = semantics;
  ro.deadline_mono_ns = cfg.o.deadline_mono_ns;
  ro.cancelled = cfg.o.cancelled;
  ro.cancel_ctx = cfg.o.cancel_ctx;
  ro.max_artifact_bytes = cfg.o.max_artifact_bytes;
  ro.max_monitor_states = cfg.o.max_monitor_states;
  TlsfGr1ReductionError err{};
  auto status = tlsf_gr1_reduce(pipeline.get(), &ro, &instance->r, &err);
  if (status != TLSF_GR1_REDUCE_OK) {
    TlsfGr1LiftStatus mapped = TLSF_GR1_LIFT_DECLINED;
    if (status == TLSF_GR1_REDUCE_LIMIT) mapped = TLSF_GR1_LIFT_LIMIT;
    if (status == TLSF_GR1_REDUCE_DEADLINE) mapped = TLSF_GR1_LIFT_DEADLINE;
    if (status == TLSF_GR1_REDUCE_CANCELLED) mapped = TLSF_GR1_LIFT_CANCELLED;
    throw Failure(mapped, err.stage[0] ? err.stage : "reduce",
                  err.message[0] ? err.message : "reduction failed");
  }
  cfg.check("provenance");
  instance->data = j::parse(std::string_view(instance->r.provenance_json,
                                            instance->r.provenance_size)).as_object();
  const O &d = instance->data;
  const O &origin = d.at("source_origin_metadata").as_object();
  if (s(d, "provenance_source") != "frontend" ||
      !origin.at("available").as_bool() ||
      s(origin, "provenance_source") != "frontend" ||
      s(origin, "source_sha256") != pipeline->source_sha256)
    decline("provenance", "ambiguous or source-unbound frontend provenance");
  std::set<std::string> signals;
  for (const char *kind : {"inputs", "outputs"})
    for (const auto &v : d.at(kind).as_array()) {
      const O &row = v.as_object();
      if (s(row, "provenance_source") != "frontend" ||
          !signals.insert(s(row, "name")).second)
        decline("provenance", "duplicate or non-frontend signal");
    }
  std::set<std::string> origins;
  for (const auto &v : d.at("source_conjuncts").as_array()) {
    const O &row = v.as_object();
    if (!origins.insert(key({s(row,"source_formula_id"), field(n(row,"generated_position"))})).second)
      decline("provenance", "duplicate source conjunct origin");
  }
  for (const auto &v : d.at("monitors").as_array()) {
    const O &row = v.as_object();
    if (s(row,"provenance_source") != "frontend" ||
        !row.contains("source_origin") || row.at("source_origin").is_null())
      decline("provenance", "missing monitor source origin");
  }
  return instance;
}
std::map<std::string, int64_t> parameters(const Instance &i) {
  std::map<std::string, int64_t> out;
  for (const auto &v : i.data.at("source_parameters").as_array()) {
    const O &r = v.as_object();
    if (!out.emplace(s(r,"name"), n(r,"value")).second)
      decline("parameters", "duplicate source parameter");
  }
  return out;
}
std::map<std::string, std::vector<const O *>> declarations(const Instance &i) {
  std::map<std::string, std::vector<const O *>> groups;
  for (const char *kind : {"inputs", "outputs"})
    for (const auto &v : i.data.at(kind).as_array()) {
      const O &r = v.as_object();
      groups[s(r,"declaration_id")].push_back(&r);
    }
  return groups;
}
std::pair<std::vector<int>, std::vector<int>> axis_members(const Instance &target,
                                                          const Instance &probe) {
  auto tg = declarations(target), pg = declarations(probe);
  if (tg.size() != pg.size()) decline("axis", "declaration ABI changed");
  std::vector<int> target_members, probe_members;
  bool changed = false;
  for (const auto &[id, trows] : tg) {
    auto iter = pg.find(id);
    if (iter == pg.end()) decline("axis", "declaration ABI changed");
    const auto &prows = iter->second;
    if (trows.size() == prows.size()) continue;
    changed = true;
    std::vector<int> ti, pi;
    for (const auto *r : trows) {
      if (s(*r,"index_role") != "element" || n(*r,"dimensions") != 1)
        decline("axis", "unproved encoding width");
      ti.push_back(ints(r->at("index_tuple").as_array()).at(0));
    }
    for (const auto *r : prows) {
      if (s(*r,"index_role") != "element" || n(*r,"dimensions") != 1)
        decline("axis", "unproved encoding width");
      pi.push_back(ints(r->at("index_tuple").as_array()).at(0));
    }
    std::sort(ti.begin(), ti.end()); std::sort(pi.begin(), pi.end());
    if (!target_members.empty() && target_members != ti) decline("axis", "inconsistent coordinates");
    if (!probe_members.empty() && probe_members != pi) decline("axis", "inconsistent coordinates");
    target_members = std::move(ti); probe_members = std::move(pi);
  }
  if (!changed) decline("axis", "parameter does not index elements");
  return {target_members, probe_members};
}
std::vector<int> monitor_indices(const O &record) {
  const O &origin = record.at("source_origin").as_object();
  auto bound = ints(origin.at("index_tuple").as_array());
  if (!bound.empty()) return bound;
  std::set<int> result;
  for (const J &v : origin.at("signal_refs").as_array()) {
    const O &ref = v.as_object();
    if (s(ref,"index_role") == "element")
      for (int coord : ints(ref.at("index_tuple").as_array())) result.insert(coord);
  }
  return {result.begin(), result.end()};
}
std::string monitor_identity(const O &r) {
  const O &o = r.at("source_origin").as_object();
  return key({s(o,"source_formula_id"), field(n(o,"source_node_id"))});
}
std::optional<std::string> symmetric_key(const O &r, const Instance &instance) {
  auto sig = r.if_contains("symmetric_signature");
  if (!sig || !sig->is_object()) return std::nullopt;
  auto groups = declarations(instance);
  std::vector<std::string> entries;
  for (const auto &[id, value] : sig->as_object()) {
    auto iter = groups.find(std::string(id));
    if (iter == groups.end() || !value.is_array()) return std::nullopt;
    std::vector<int> counts = ints(value.as_array());
    int width = int(iter->second.size());
    std::string normal;
    if (counts.empty()) normal = "empty";
    else {
      bool interval = true;
      for (size_t k = 1; k < counts.size(); k++)
        interval &= counts[k] == counts[0] + int(k);
      if (interval)
        normal = key({"interval", field(counts.front()), counts.back() == width ? "all" : field(counts.back())});
      else {
        std::vector<std::string> bits{"set"};
        for (int x : counts) bits.push_back(x == width ? "all" : field(x));
        normal = join(bits);
      }
    }
    entries.push_back(key({std::string(id), normal}));
  }
  std::sort(entries.begin(), entries.end());
  return join(entries);
}
struct Modes { std::map<std::string, bool> symmetric; };
Modes target_modes(const Instance &target) {
  Modes modes;
  for (const J &v : target.data.at("monitors").as_array()) {
    const O &r = v.as_object();
    modes.symmetric[monitor_identity(r)] = s(r,"arity_kind") == "bus_wide" &&
                                             symmetric_key(r, target).has_value();
  }
  return modes;
}
std::string monitor_key(const O &r, const Instance &i, const Modes &m,
                        const Config &cfg) {
  const O &o = r.at("source_origin").as_object();
  bool symmetric = false;
  auto mode = m.symmetric.find(monitor_identity(r));
  if (mode != m.symmetric.end()) symmetric = mode->second;
  else symmetric = s(r,"arity_kind") == "bus_wide";
  std::string semantic;
  std::string kind = "bounded_support";
  if (symmetric) {
    auto signature=symmetric_key(r, i);
    if (signature) { semantic=*signature; kind = "symmetric"; }
  }
  if (kind == "bounded_support") {
    if (monitor_indices(r).size() > cfg.o.max_predicate_arity)
      decline("bus_schema", "unproved large template");
    semantic = s(r,"template");
  }
  return key({s(o,"source_formula_id"), field(n(o,"source_node_id")),
              s(r,"side"), s(r,"role"), s(r,"mp_class"), kind,
              field(n(r,"state_count")), semantic});
}
bool monitor_is_symmetric(const O &r, const Instance &i, const Modes &m) {
  auto mode=m.symmetric.find(monitor_identity(r));
  bool requested=mode!=m.symmetric.end()?mode->second:s(r,"arity_kind")=="bus_wide";
  return requested && symmetric_key(r,i).has_value();
}
std::string structural_shape(const Instance &i, const Modes &m, const Config &cfg) {
  std::set<std::string> decls, sources, monitors;
  for (const char *kind : {"inputs", "outputs"})
    for (const J &v : i.data.at(kind).as_array()) {
      const O &r = v.as_object();
      decls.insert(key({s(r,"declaration_id"),s(r,"direction"),
                        field(n(r,"dimensions")),s(r,"index_role"),s(r,"width_kind")}));
    }
  for (const J &v : i.data.at("source_conjuncts").as_array()) {
    const O &r = v.as_object();
    std::vector<std::string> binders;
    for (const J &b : r.at("bindings").as_array())
      binders.push_back(field(n(b.as_object(),"binder_id")));
    sources.insert(key({s(r,"source_formula_id"),field(n(r,"source_node_id")),join(binders)}));
  }
  for (const J &v : i.data.at("monitors").as_array())
    monitors.insert(monitor_key(v.as_object(),i,m,cfg));
  return key({join({decls.begin(),decls.end()}),join({sources.begin(),sources.end()}),
              join({monitors.begin(),monitors.end()}),s(i.data,"latch_encoding")});
}
using Roles = std::map<int,std::string>;
Roles role_signatures(const Instance &i, const Modes &m, const Config &cfg) {
  const auto &members = i.members;
  struct Count { int count = 0; int arity = 0; bool normalize = false; };
  std::map<int,std::map<std::string,Count>> incidents;
  for (int coord : members) incidents[coord];
  auto add = [&](int coord, std::string k, int arity, bool normalize) {
    auto it = incidents.find(coord);
    if (it != incidents.end()) {
      auto &c = it->second[k]; c.count++; c.arity = arity; c.normalize = normalize;
    }
  };
  for (const char *kind : {"inputs", "outputs"})
    for (const J &v : i.data.at(kind).as_array()) {
      const O &r = v.as_object();
      if (s(r,"index_role") == "element" && r.at("index_tuple").as_array().size() == 1)
        add(ints(r.at("index_tuple").as_array())[0],
            key({"declaration",s(r,"declaration_id")}),1,false);
    }
  for (const J &v : i.data.at("monitors").as_array()) {
    const O &r = v.as_object();
    std::string mk = monitor_key(r,i,m,cfg);
    if (monitor_is_symmetric(r,i,m)) continue;
    auto indices = monitor_indices(r);
    int arity = int(r.at("source_origin").as_object().at("index_tuple").as_array().size());
    for (size_t p=0; p<indices.size();p++)
      add(indices[p],key({"monitor",mk,field(p),field(arity)}),arity,true);
  }
  for (const J &v : i.data.at("source_conjuncts").as_array()) {
    const O &r = v.as_object();
    std::vector<int> bindings;
    for (const J &b : r.at("bindings").as_array())
      bindings.push_back(int(n(b.as_object(),"value")));
    std::vector<std::string> shapes;
    for (const J &ref : r.at("signal_refs").as_array()) {
      const O &sr = ref.as_object();
      std::vector<std::string> relation;
      for (int coordinate : ints(sr.at("index_tuple").as_array())) {
        std::vector<std::string> positions;
        for (size_t p=0;p<bindings.size();p++)
          if (bindings[p] == coordinate) positions.push_back(field(p));
        if (!positions.empty()) relation.push_back(key({"bound",join(positions)}));
        else if (!bindings.empty()) {
          std::vector<std::string> offsets;
          for (int bound : bindings) offsets.push_back(field(coordinate-bound));
          relation.push_back(key({"relative",join(offsets)}));
        } else relation.push_back(key({"fixed",field(coordinate)}));
      }
      shapes.push_back(key({s(sr,"declaration_id"),join(relation)}));
    }
    std::sort(shapes.begin(),shapes.end());
    std::string shape = key({s(r,"source_formula_id"),field(n(r,"source_node_id")),join(shapes)});
    for (size_t p=0;p<bindings.size();p++)
      add(bindings[p],key({"conjunct",shape,field(p),field(bindings.size())}),
          int(bindings.size()),true);
  }
  Roles out;
  for (auto &[coord, counts] : incidents) {
    std::vector<std::string> bits;
    for (const auto &[k,c] : counts) {
      std::string degree = c.normalize && c.arity > 1 && c.count == int(members.size())-1
          ? "all_except_self" : c.count == 1 ? "one" :
            c.count == int(members.size()) ? "all" : key({"count",field(c.count)});
      bits.push_back(key({k,degree}));
    }
    out[coord] = join(bits);
  }
  return out;
}

struct Window {
  std::string axis;
  std::vector<int> sizes;
  std::vector<std::unique_ptr<Instance>> seeds;
  Modes modes;
};
#ifdef TLSF_GR1_LIFT_TEST_FAULT
thread_local int lift_test_fault = 0;
#endif
void validate_window(const Window &window, const Instance &target) {
  if (window.sizes.size()!=window.seeds.size() || window.sizes.size()<2)
    decline("seed_window","invalid selected seed count");
  for (size_t p=0;p<window.seeds.size();p++) {
    const Instance &seed=*window.seeds[p];
    auto choice=seed.overrides.find(window.axis);
    if (choice==seed.overrides.end() || choice->second!=window.sizes[p] ||
        seed.members!=axis_members(target,seed).second)
      decline("seed_window","selected seed choice disagrees with artifact");
    if (p && window.sizes[p]!=window.sizes[p-1]+1)
      decline("seed_window","selected seeds are not consecutive");
  }
}
Window discover(const uint8_t *source, size_t size, Instance &target,
                TlsfGr1ReductionSemantics semantics, const Config &cfg) {
  auto axes = parameters(target);
  if (axes.empty()) decline("parameters", "absent");
  for (const auto &[axis, value] : axes) {
    struct Probe { int size; std::unique_ptr<Instance> inst; };
    std::vector<Probe> probes;
    for (int k=1; k<value && k<=int(cfg.o.max_sizes_per_axis); k++) {
      cfg.check("seed_window");
      auto values = axes; values[axis] = k;
      try {
        auto probe = lower(source,size,values,semantics,cfg);
        auto coords = axis_members(target,*probe);
        probe->members = std::move(coords.second);
        probes.push_back({k,std::move(probe)});
      } catch (const Failure &e) {
        if (e.status == TLSF_GR1_LIFT_DEADLINE || e.status == TLSF_GR1_LIFT_CANCELLED ||
            e.status == TLSF_GR1_LIFT_LIMIT) throw;
      }
    }
    Modes modes = target_modes(target);
    std::string target_shape=structural_shape(target,modes,cfg);
    for (size_t p=1;p<probes.size();p++) {
      if (probes[p].size != probes[p-1].size+1) continue;
      try {
        Instance &left=*probes[p-1].inst, &right=*probes[p].inst;
        if (structural_shape(left,modes,cfg)!=target_shape ||
            structural_shape(right,modes,cfg)!=target_shape) continue;
        auto coords=axis_members(target,left);
        target.members=std::move(coords.first);
        if (left.members.size()>=right.members.size() ||
            right.members.size()>=target.members.size()) continue;
        std::vector<size_t> selected{p-1,p};
        if (cfg.o.seed_confirmation != 2 && p+1<probes.size() &&
            probes[p+1].size==probes[p].size+1) {
          if (structural_shape(*probes[p+1].inst,modes,cfg)!=target_shape) continue;
          selected.push_back(p+1);
        }
        auto classes=[&](Instance &i) {
          Roles roles=role_signatures(i,modes,cfg);
          std::set<std::string> x;
          for (const auto &[index,signature] : roles) x.insert(signature);
          return x;
        };
        auto expected=classes(left);
        bool stable=true;
        for (size_t pos:selected) stable &= classes(*probes[pos].inst)==expected;
        if (!stable) continue;
        (void)role_signatures(target,modes,cfg);
        Window result; result.axis=axis; result.modes=modes;
        for (size_t pos:selected) {
          result.sizes.push_back(probes[pos].size);
          result.seeds.push_back(std::move(probes[pos].inst));
        }
        return result;
      } catch (const Failure &e) {
        if (e.status==TLSF_GR1_LIFT_DEADLINE || e.status==TLSF_GR1_LIFT_CANCELLED ||
            e.status==TLSF_GR1_LIFT_LIMIT) throw;
      }
    }
  }
  decline("seed_window", "no stable index axis");
}
void solve_seed(Instance &i, const Config &cfg) {
  cfg.check("seed_solve");
  char reason[256]{};
  if (!tlsf_gr1_validate_game(i.r.game,reason,sizeof reason))
    decline("seed_solve",reason);
  auto copy = parse_aig(i.r.aag,i.r.aag_size);
  OxiddFailure failure{};
  OxiddSolveOptions options = oxidd_solve_options_default();
  options.node_cap=cfg.o.solver_nodes;
  options.cache_cap=cfg.o.solver_cache;
  options.deadline_mono_ns=cfg.o.deadline_mono_ns;
  options.cancelled=cfg.o.cancelled;
  options.cancel_ctx=cfg.o.cancel_ctx;
  options.max_artifact_bytes=cfg.o.max_artifact_bytes;
  options.failure=&failure;
  char *cert=nullptr,*meta=nullptr;
  size_t cert_size=0,meta_size=0;
  Gr1CertificateOptions export_options{};
  export_options.semantics=GR1_CERTIFICATE_SEMANTICS_EXACT;
  export_options.aag_bytes=&cert;
  export_options.aag_size=&cert_size;
  export_options.json_bytes=&meta;
  export_options.json_size=&meta_size;
  export_options.max_artifact_bytes=cfg.o.max_artifact_bytes;
  int unreal=0;
  Aig *strategy = solve_gr1_oxidd_ex_with_certificate(
      copy.release(), &unreal, &options, &export_options);
  aig_free(strategy);
  std::unique_ptr<char,decltype(&free)> cert_guard(cert,&free),meta_guard(meta,&free);
  if (!strategy || unreal || export_options.failed || !cert || !meta) {
    if (failure.kind==OXIDD_FAILURE_DEADLINE)
      throw Failure(TLSF_GR1_LIFT_DEADLINE,"seed_solve","deadline exceeded");
    if (failure.kind==OXIDD_FAILURE_CANCELLED)
      throw Failure(TLSF_GR1_LIFT_CANCELLED,"seed_solve","cancelled");
    if (failure.kind==OXIDD_FAILURE_BDD || failure.kind==OXIDD_FAILURE_ARTIFACT_LIMIT ||
        failure.kind==OXIDD_FAILURE_HOST)
      throw Failure(TLSF_GR1_LIFT_LIMIT,"seed_solve","solver capacity exhausted");
    decline("seed_solve","no system certificate");
  }
  cfg.bytes(cert_size,"seed_solve"); cfg.bytes(meta_size,"seed_solve");
  i.cert_aag.assign(cert,cert_size);
  i.cert_json.assign(meta,meta_size);
  i.cert_meta=j::parse(i.cert_json).as_object();
  if (s(i.cert_meta,"status")!="realizable" || s(i.cert_meta,"side")!="system" ||
      s(i.cert_meta,"reduction_semantics")!="exact")
    decline("seed_solve","certificate metadata mismatch");
  i.cert=parse_aig(i.cert_aag.data(),i.cert_aag.size());
}
struct Variable {
  int index;
  std::string kind,prefix;
  std::vector<int> indices;
  std::set<int> owners;
};
struct Goal { int number,owner; std::string key; };
struct GameView {
  Instance *inst;
  Modes modes;
  Roles roles;
  std::vector<Variable> variables;
  std::vector<Goal> goals;
  std::vector<bool> controls;
  std::map<std::string,int> output_by_name;
  uint32_t states,inputs,fairness;
  GameView(Instance &i, const Modes &m, const Config &cfg) : inst(&i), modes(m),
      roles(role_signatures(i,m,cfg)), states(aig_num_latches(i.r.game)),
      inputs(aig_num_inputs(i.r.game)), fairness(aig_num_fairness(i.r.game)) {
    auto &data=i.data;
    std::map<uint32_t,std::pair<const O *,size_t>> latch_records;
    for (const J &v:data.at("monitors").as_array()) {
      const O &r=v.as_object();
      const A &lits=r.at("latch_literals").as_array();
      if (!lits.empty() && lits.size()!=size_t(n(r,"state_count")))
        decline("schema_abi","monitor inventory");
      for (size_t state=0;state<lits.size();state++)
        if (!latch_records.emplace(uint32_t(num(lits[state])),
                                   std::make_pair(&r,state)).second)
          decline("schema_abi","duplicate monitor latch literal");
    }
    uint32_t violated=UINT32_MAX;
    if (s(data,"semantics")=="strict" && !data.at("violated_latch_literal").is_null())
      violated=uint32_t(num(data.at("violated_latch_literal")));
    for (uint32_t p=0;p<states;p++) {
      uint32_t lit=0;
      aig_latch_at(i.r.game,p,&lit,nullptr,nullptr);
      if (lit==violated) {
        variables.push_back({int(p),"state","strict_release",{}, {}});
        continue;
      }
      auto found=latch_records.find(lit);
      if (found==latch_records.end()) decline("schema_abi","unmatched latch literal");
      const O &r=*found->second.first;
      auto indices=monitor_indices(r);
      if (monitor_is_symmetric(r,i,m)) indices.clear();
      std::set<int> owners;
      for (int x:indices) if (roles.count(x)) owners.insert(x);
      variables.push_back({int(p),"state",key({monitor_key(r,i,m,cfg),field(found->second.second)}),
                           indices,std::move(owners)});
    }
    if (latch_records.size()+(violated!=UINT32_MAX)!=states)
      decline("schema_abi","latch inventory");
    std::map<uint32_t,const O *> signals;
    for (const char *kind:{"inputs","outputs"})
      for (const J &v:data.at(kind).as_array()) {
        const O &r=v.as_object();
        if (!signals.emplace(uint32_t(n(r,"game_literal")),&r).second)
          decline("schema_abi","duplicate game literal");
      }
    if (signals.size()!=inputs) decline("schema_abi","signal inventory");
    for (uint32_t p=0;p<inputs;p++) {
      uint32_t lit=0;
      aig_input_name(i.r.game,p,&lit);
      auto it=signals.find(lit);
      if (it==signals.end()) decline("schema_abi","game signal unmatched");
      const O &r=*it->second;
      if (s(r,"direction")!="input" && s(r,"direction")!="output")
        decline("schema_abi","invalid signal direction");
      controls.push_back(s(r,"direction")=="output");
      auto indices=ints(r.at("index_tuple").as_array());
      std::set<int> owners;
      if (s(r,"index_role")=="element")
        for (int x:indices) if (roles.count(x)) owners.insert(x);
      variables.push_back({int(states+p),"letter",key({s(r,"direction"),s(r,"declaration_id")}),
                           indices,std::move(owners)});
    }
    if (i.cert) {
      if (aig_num_inputs(i.cert.get())!=variables.size() ||
          n(i.cert_meta.at("counts").as_object(),"sampling_latches")!=0 ||
          n(i.cert_meta.at("counts").as_object(),"original_game_latches")!=states)
        decline("schema_abi","certificate input mismatch");
      for (uint32_t p=0;p<variables.size();p++) {
        const char *actual=aig_input_name(i.cert.get(),p,nullptr);
        const char *expected=p<states?aig_latch_name(i.r.game,p):
            aig_input_name(i.r.game,p-states,nullptr);
        if (!actual || !expected || strcmp(actual,expected))
          decline("schema_abi","certificate input mismatch");
      }
      for (uint32_t p=0;p<aig_num_outputs(i.cert.get());p++) {
        const char *name=aig_output_at(i.cert.get(),p,nullptr);
        if (name) output_by_name[name]=int(p);
      }
    }
    std::map<int,const O *> justice;
    for (const J &v:data.at("monitors").as_array())
      if (s(v.as_object(),"role")=="justice") {
        const O &r=v.as_object();
        if (!r.contains("justice_index") ||
            !justice.emplace(int(n(r,"justice_index")),&r).second)
          decline("schema_abi","duplicate justice ID");
      }
    if (s(data,"semantics")=="strict" && justice.empty() && aig_num_justice(i.r.game)==1) {
      goals.push_back({0,-1,"implicit_true_justice"});
    } else {
      if (justice.size()!=aig_num_justice(i.r.game))
        decline("schema_abi","justice inventory");
      for (size_t p=0;p<justice.size();p++) {
        auto found=justice.find(int(p));
        if (found==justice.end()) decline("schema_abi","missing justice ID");
        const O &r=*found->second;
        auto indices=ints(r.at("source_origin").as_object().at("index_tuple").as_array());
        if (indices.size()>1) decline("schema_abi","multi-index goal");
        int owner=indices.size()==1 && roles.count(indices[0])?indices[0]:-1;
        std::string role=owner<0?"null":roles.at(owner);
        goals.push_back({int(p),owner,key({monitor_key(r,i,m,cfg),role})});
      }
    }
    for (uint32_t goal=0;goal<aig_num_justice(i.r.game);goal++) {
      uint32_t count=0; aig_justice_at(i.r.game,goal,nullptr,&count);
      if (count!=1) decline("schema_abi","multi-member justice");
    }
  }
  int levels(const Goal &goal) const {
    return int(num(inst->cert_meta.at("counts").as_object().at("levels_per_goal").as_array().at(goal.number)));
  }
  uint32_t output(const std::string &name) const {
    if (!inst->cert || !output_by_name.count(name)) decline("schema_abi","missing seed predicate");
    uint32_t lit=aig_output_lit(inst->cert.get(),name.c_str());
    if (lit==UINT32_MAX) decline("schema_abi","missing seed predicate");
    return lit;
  }
};
struct B {
  oxidd_bdd_t v{};
  B()=default;
  explicit B(oxidd_bdd_t f):v(f) {
    if (!v._p) throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","OxiDD allocation failed");
  }
  B(const B &other):v(oxidd_bdd_ref(other.v)){}
  B(B &&other) noexcept :v(other.v){other.v={};}
  B &operator=(const B &other){
    if(this!=&other){oxidd_bdd_unref(v);v=oxidd_bdd_ref(other.v);} return *this;
  }
  B &operator=(B &&other) noexcept {
    if(this!=&other){oxidd_bdd_unref(v);v=other.v;other.v={};} return *this;
  }
  ~B(){oxidd_bdd_unref(v);}
};
bool same(const B &a,const B &b){return bdd_eq(a.v,b.v);}
using Handle=std::pair<const void *,size_t>;
Handle handle(const B &v){return {v.v._p,v.v._i};}
class Schema {
  oxidd_bdd_manager_t manager{};
  const Config *cfg;
  size_t calls=0;
  std::map<std::string,int> normal;
  std::map<int,std::string> reverse_normal;
public:
  Schema(const Config &config,uint32_t initial):cfg(&config){
    manager=oxidd_bdd_manager_new(cfg->o.schema_nodes,cfg->o.schema_cache,1);
    if(!manager._p) throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","cannot create OxiDD manager");
    grow(initial);
  }
  ~Schema(){oxidd_bdd_manager_unref(manager);}
  Schema(const Schema&)=delete;
  void set_config(const Config &config){cfg=&config;}
  void tick(const char *stage="schema") {
    if((++calls&127u)==0){cfg->check(stage);
      if(oxidd_bdd_manager_approx_num_inner_nodes(manager)>cfg->o.schema_nodes)
        throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","node cap exceeded");}
  }
  int width() const {return int(oxidd_bdd_manager_num_vars(manager));}
  void grow(int count){
    if(count<=width()) return;
    auto range=oxidd_bdd_manager_add_vars(manager,count-width());
    if(int(range.end)!=count) throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","BDD variable limit");
  }
  B t(){tick();return B(oxidd_bdd_true(manager));}
  B f(){tick();return B(oxidd_bdd_false(manager));}
  B var(int i){grow(i+1);tick();return B(oxidd_bdd_var(manager,i));}
  B neg(const B &a){tick();return B(oxidd_bdd_not(a.v));}
  B land(const B &a,const B &b){tick();return B(oxidd_bdd_and(a.v,b.v));}
  B lor(const B &a,const B &b){tick();return B(oxidd_bdd_or(a.v,b.v));}
  B ite(const B &c,const B &a,const B &b){tick();return B(oxidd_bdd_ite(c.v,a.v,b.v));}
  B exists(const B &a,const B &cube){tick();return B(oxidd_bdd_exists(a.v,cube.v));}
  B cube(const std::set<int> &vars){B x=t();for(int v:vars)x=land(x,var(v));return x;}
  int normal_var(const std::string &k){
    auto it=normal.find(k);if(it!=normal.end())return it->second;
    int index=width();grow(index+1);normal[k]=index;reverse_normal[index]=k;return index;
  }
  const std::string &normal_key(int index)const{return reverse_normal.at(index);}
  std::set<int> support(const B &root){
    std::set<int> vars;
    std::set<Handle> visited;
    std::function<void(const B&)> visit=[&](const B &node){
      tick();
      if(oxidd_bdd_node_level(node.v)==(oxidd_level_no_t)-1)return;
      if(!visited.insert(handle(node)).second)return;
      vars.insert(int(oxidd_bdd_node_var(node.v)));
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      visit(hi);visit(lo);
    }; visit(root);return vars;
  }
  B relabel(const B &root,const std::map<int,int> &mapping){
    auto supp=support(root);
    for(int v:supp)if(!mapping.count(v))decline("schema_abi","unmapped BDD support");
    std::map<Handle,B> memo;
    std::function<B(const B&)> visit=[&](const B &node)->B{
      tick();
      if(oxidd_bdd_node_level(node.v)==(oxidd_level_no_t)-1)return node;
      auto h=handle(node);auto it=memo.find(h);if(it!=memo.end())return it->second;
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      B result=ite(var(mapping.at(int(oxidd_bdd_node_var(node.v)))),visit(hi),visit(lo));
      memo.emplace(h,result);return result;
    };return visit(root);
  }
  B from_aig(const Aig *aig,uint32_t root,bool game=false){
    std::map<uint32_t,B> leaves,memo;
    std::map<uint32_t,std::pair<uint32_t,uint32_t>> gates;
    uint32_t nstate=game?aig_num_latches(aig):0;
    if(game)for(uint32_t p=0;p<nstate;p++){
      uint32_t lit;aig_latch_at(aig,p,&lit,nullptr,nullptr);leaves.emplace(lit/2,var(p));
    }
    for(uint32_t p=0;p<aig_num_inputs(aig);p++){
      uint32_t lit;aig_input_name(aig,p,&lit);leaves.emplace(lit/2,var(nstate+p));
    }
    for(uint32_t p=0;p<aig_num_ands(aig);p++){
      uint32_t lhs,left,right;aig_and_at(aig,p,&lhs,&left,&right);
      gates.emplace(lhs/2,std::pair{left,right});
    }
    std::function<B(uint32_t)> value=[&](uint32_t lit)->B{
      tick();
      if(lit==0)return f();
      if(lit==1)return t();
      if(lit&1)return neg(value(lit^1));
      uint32_t variable=lit/2;
      if(auto it=leaves.find(variable);it!=leaves.end())return it->second;
      if(auto it=memo.find(variable);it!=memo.end())return it->second;
      auto gate=gates.find(variable);
      if(gate==gates.end())decline("schema_abi","AIG root references missing gate");
      B result=land(value(gate->second.first),value(gate->second.second));
      memo.emplace(variable,result);
      return result;
    };
    return value(root);
  }
  uint32_t to_aig(Aig *aig,const B &root,const std::map<int,uint32_t> &lits){
    std::map<Handle,uint32_t> memo;
    std::function<uint32_t(const B&)> visit=[&](const B &node)->uint32_t{
      tick("certificate_export");
      if(oxidd_bdd_node_level(node.v)==(oxidd_level_no_t)-1)
        return oxidd_bdd_satisfiable(node.v)?AIG_TRUE:AIG_FALSE;
      auto h=handle(node);auto it=memo.find(h);if(it!=memo.end())return it->second;
      int variable=int(oxidd_bdd_node_var(node.v));
      auto found=lits.find(variable);
      if(found==lits.end())decline("candidate","unmapped BDD variable");
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      uint32_t x=found->second;
      uint32_t result=aig_or(aig,aig_and(aig,x,visit(hi)),
                             aig_and(aig,aig_not(x),visit(lo)));
      memo.emplace(h,result);return result;
    };return visit(root);
  }
};
std::string normal_key(const Variable &v,const std::map<int,int> &slots){
  std::vector<std::string> coords;
  for(int x:v.indices){
    auto it=slots.find(x);
    coords.push_back(it==slots.end()?key({"fixed",field(x)}):key({"slot",field(it->second)}));
  }
  return key({v.kind,v.prefix,join(coords)});
}
std::vector<int> ordered(const GameView &view,const std::vector<int> &subset,
                         const Goal *goal){
  std::vector<int> out=subset;
  std::sort(out.begin(),out.end(),[&](int a,int b){
    if(goal && a==goal->owner)return true;
    if(goal && b==goal->owner)return false;
    return std::tie(view.roles.at(a),a)<std::tie(view.roles.at(b),b);
  });
  return out;
}
std::string group_key(const GameView &view,const std::vector<int> &subset,const Goal *goal){
  std::vector<std::string> roles,relation;
  for(int x:subset){roles.push_back(view.roles.at(x));relation.push_back(goal&&goal->owner==x?"goal":"other");}
  return key({join(roles),join(relation)});
}
uint64_t choose_bounded(size_t n,size_t k,uint32_t cap){
  if(k>n)return 0;
  uint64_t count=1;
  for(size_t p=1;p<=k;p++){
    if(count>uint64_t(cap)*p/(n-k+p))return uint64_t(cap)+1;
    count=count*(n-k+p)/p;
  }
  return count;
}
template<typename Fn> void subsets(const std::vector<int> &members,int arity,Fn &&fn){
  std::vector<int> chosen;
  std::function<void(size_t)> visit=[&](size_t start){
    if(int(chosen.size())==arity){fn(chosen);return;}
    for(size_t p=start;p<members.size();p++){
      chosen.push_back(members[p]);visit(p+1);chosen.pop_back();
    }
  };visit(0);
}
using Template=std::map<std::string,B>;
Template project(Schema &bdd,const GameView &view,const B &function,int arity,
                 const Goal *goal,const Config &cfg){
  if(choose_bounded(view.inst->members.size(),arity,cfg.o.max_subsets_per_predicate)>
     cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","subset count limit");
  Template result;
  B rebuilt=bdd.t();
  auto support=bdd.support(function);
  subsets(view.inst->members,arity,[&](const std::vector<int> &selected){
    cfg.check("schema");
    auto subset=ordered(view,selected,goal);
    std::set<int> set(subset.begin(),subset.end());
    std::map<int,int> slots;
    for(size_t p=0;p<subset.size();p++)slots[subset[p]]=int(p);
    std::set<int> keep,drop;
    std::map<int,int> mapping,back;
    for(const auto &v:view.variables){
      if(std::includes(set.begin(),set.end(),v.owners.begin(),v.owners.end())){
        keep.insert(v.index);
        int normalized=bdd.normal_var(normal_key(v,slots));
        mapping[v.index]=normalized;
        if(!back.emplace(normalized,v.index).second)
          decline("schema_abi","duplicate normalized variable");
      }
    }
    for(int v:support)if(!keep.count(v))drop.insert(v);
    B projected=drop.empty()?function:bdd.exists(function,bdd.cube(drop));
    B normalized=bdd.relabel(projected,mapping);
    auto group=group_key(view,subset,goal);
    auto found=result.find(group);
    if(found!=result.end() && !same(found->second,normalized))
      decline("schema","within-role projection disagreement");
    result.insert_or_assign(group,normalized);
    rebuilt=bdd.land(rebuilt,bdd.relabel(normalized,back));
  });
  if(!same(rebuilt,function))decline("schema","predicate not exactly reconstructed");
  return result;
}
struct Learned {Template templ;int arity;};
Learned learn(Schema &bdd,const std::vector<GameView> &seeds,
              const std::vector<std::string> &names,
              const std::vector<const Goal *> &goals,const Config &cfg){
  int limit=int(cfg.o.max_predicate_arity);
  for(const auto &seed:seeds)limit=std::min(limit,int(seed.inst->members.size()));
  for(int arity=0;arity<=limit;arity++){
    cfg.check("schema");
    bool has_larger=false;
    for(const auto &seed:seeds)has_larger |= seed.inst->members.size()>size_t(arity);
    if(!has_larger)continue;
    std::vector<Template> observed;
    try {
      for(size_t p=0;p<seeds.size();p++){
        const auto &seed=seeds[p];
        B predicate=bdd.from_aig(seed.inst->cert.get(),seed.output(names[p]));
        observed.push_back(project(bdd,seed,predicate,arity,goals[p],cfg));
      }
    } catch(const Failure &e) {
      if(e.status!=TLSF_GR1_LIFT_DECLINED)throw;
      continue;
    }
    bool equal=true;
    for(size_t p=1;p<observed.size();p++){
      if(observed[p].size()!=observed[0].size()){equal=false;break;}
      for(const auto &[group,fun]:observed[0]){
        auto it=observed[p].find(group);
        if(it==observed[p].end() || !same(fun,it->second)){equal=false;break;}
      }
    }
    if(equal)return {std::move(observed[0]),arity};
  }
  decline("schema","no bounded exact template");
}
B instantiate(Schema &bdd,const GameView &target,const Learned &learned,
              const Goal *goal,const Config &cfg){
  if(choose_bounded(target.inst->members.size(),learned.arity,cfg.o.max_subsets_per_predicate)>
     cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT,"schema_capacity","target subset count limit");
  B result=bdd.t();
  subsets(target.inst->members,learned.arity,[&](const std::vector<int> &selected){
    cfg.check("instantiate");
    auto subset=ordered(target,selected,goal);
    auto it=learned.templ.find(group_key(target,subset,goal));
    if(it==learned.templ.end())decline("instantiate","missing role template");
    std::set<int> set(subset.begin(),subset.end());
    std::map<int,int> slots;
    for(size_t p=0;p<subset.size();p++)slots[subset[p]]=int(p);
    std::map<std::string,int> concrete;
    for(const auto &v:target.variables)
      if(std::includes(set.begin(),set.end(),v.owners.begin(),v.owners.end()))
        concrete[normal_key(v,slots)]=v.index;
    std::map<int,int> mapping;
    for(int variable:bdd.support(it->second)){
      auto found=concrete.find(bdd.normal_key(variable));
      if(found==concrete.end())decline("instantiate","missing target variable");
      mapping[variable]=found->second;
    }
    result=bdd.land(result,bdd.relabel(it->second,mapping));
  });return result;
}
struct LearnedCertificate {
  std::map<std::string,B> predicates;
  std::map<std::string,int> arities;
  std::vector<int> depths;
};
LearnedCertificate learn_certificate(Schema &bdd,const std::vector<GameView> &seeds,
                                     const GameView &target,const Config &cfg){
  if(seeds.empty())decline("schema","no seeds");
  for(const auto &seed:seeds){
    if(seed.fairness!=target.fairness)decline("schema_abi","fairness changed");
    std::set<std::string> left,right;
    for(const auto &[coord,role]:seed.roles)left.insert(role);
    for(const auto &[coord,role]:target.roles)right.insert(role);
    if(left!=right)decline("schema_abi","role classes changed");
  }
  LearnedCertificate out;
  // Rank depth is a property of the selected solved seeds. Check it before
  // predicate learning so an unstable family has a precise decline stage.
  for (const Goal &goal:target.goals) {
    int depth=-1;
    for (const auto &seed:seeds) {
      const Goal *found=nullptr;
      for (const Goal &g:seed.goals) if (g.key==goal.key) {found=&g;break;}
      if (!found) decline("schema_abi","goal class absent");
      int current=seed.levels(*found);
      if (current<1) decline("schema","empty rank depth");
      if (depth>=0 && current!=depth)
        throw Failure(TLSF_GR1_LIFT_DECLINED,"schema",
                      "rank depth changed from "+field(depth)+" to "+field(current));
      depth=current;
    }
    out.depths.push_back(depth);
  }
  auto inv=learn(bdd,seeds,std::vector<std::string>(seeds.size(),"inv"),
                 std::vector<const Goal *>(seeds.size(),nullptr),cfg);
  out.predicates.emplace("inv",instantiate(bdd,target,inv,nullptr,cfg));
  out.arities["inv"]=inv.arity;
  for(size_t goal_pos=0;goal_pos<target.goals.size();goal_pos++){
    const Goal &goal=target.goals[goal_pos];
    std::vector<const Goal *> aligned;
    for(const auto &seed:seeds){
      const Goal *found=nullptr;
      for(const Goal &g:seed.goals)if(g.key==goal.key){found=&g;break;}
      if(!found)decline("schema_abi","goal class absent");
      aligned.push_back(found);
    }
    int depth=out.depths[goal_pos];
    const uint32_t *members=nullptr;uint32_t count=0;
    aig_justice_at(target.inst->r.game,goal.number,&members,&count);
    if(count!=1)decline("schema_abi","multi-member justice");
    out.predicates.emplace("goal_"+field(goal.number),
                           bdd.from_aig(target.inst->r.game,members[0],true));
    for(int level=0;level<depth;level++){
      B y=bdd.f();
      for(int fair=0;fair<int(std::max(1u,target.fairness));fair++){
        std::vector<std::string> names;
        for(const Goal *g:aligned)
          names.push_back("x_"+field(g->number)+"_"+field(level)+"_"+field(fair));
        auto learned=learn(bdd,seeds,names,aligned,cfg);
        std::string name="x_"+field(goal.number)+"_"+field(level)+"_"+field(fair);
        B x=instantiate(bdd,target,learned,&goal,cfg);
        y=bdd.lor(y,x);
        out.predicates.emplace(name,std::move(x));
        out.arities[name]=learned.arity;
      }
      out.predicates.emplace("y_"+field(goal.number)+"_"+field(level),std::move(y));
    }
  }
  return out;
}
struct Candidate {
  std::string game,certificate,certificate_json,policy,policy_json,check_json,evidence;
  TlsfGr1CheckMethod method=TLSF_GR1_CHECK_CERTIFICATE;
  TlsfGr1CheckVerdict verdict=TLSF_GR1_CHECK_UNKNOWN;
};
J certificate_sidecar(const GameView &target,const LearnedCertificate &learned,
                      const Aig *certificate,TlsfGr1ReductionSemantics semantics){
  const Aig *game=target.inst->r.game;
  uint32_t nstate=target.states,nin=target.inputs,ngoals=uint32_t(target.goals.size());
  uint32_t nu=0,nc=0;
  A state,unc,con,outputs,goals,counters,depths;
  for(uint32_t p=0;p<nstate;p++){
    uint32_t cur,next,reset;aig_latch_at(game,p,&cur,&next,&reset);
    state.emplace_back(O{{"certificate_input",p},{"name",aig_latch_name(game,p)},
                         {"game_latch",p},{"game_literal",cur},{"next_game_literal",next},
                         {"reset",reset},{"solver_added",false}});
  }
  for(uint32_t p=0;p<nin;p++){
    uint32_t lit;const char *name=aig_input_name(game,p,&lit);
    O row{{"certificate_input",nstate+p},{"game_input",p},{"game_literal",lit},
          {"name",name}};
    if(target.controls[p]){con.emplace_back(std::move(row));nc++;}
    else{unc.emplace_back(std::move(row));nu++;}
  }
  outputs.emplace_back(O{{"name","inv"},{"kind","winning_region"}});
  for(uint32_t goal=0;goal<ngoals;goal++){
    std::string name="goal_"+field(goal);
    outputs.emplace_back(O{{"name",name},{"kind","goal"},{"goal",goal}});
  }
  for(uint32_t goal=0;goal<ngoals;goal++){
    depths.emplace_back(learned.depths[goal]);
    for(int level=0;level<learned.depths[goal];level++){
      std::string name="y_"+field(goal)+"_"+field(level);
      outputs.emplace_back(O{{"name",name},{"kind","mu_level"},
                             {"goal",goal},{"level",level}});
    }
  }
  for(uint32_t goal=0;goal<ngoals;goal++)
    for(int level=0;level<learned.depths[goal];level++)
      for(uint32_t fair=0;fair<std::max(1u,target.fairness);fair++){
        std::string name="x_"+field(goal)+"_"+field(level)+"_"+field(fair);
        outputs.emplace_back(O{{"name",name},{"kind","nu_level"},
                               {"goal",goal},{"level",level},{"fairness",fair}});
      }
  for(uint32_t goal=0;goal<ngoals;goal++){
    std::string name="move_"+field(goal);
    outputs.emplace_back(O{{"name",name},{"kind","move_relation"},{"goal",goal}});
    goals.emplace_back(O{{"goal",goal},{"justice_record",goal},{"record_member",0}});
    counters.emplace_back(O{{"strategy_latch",nstate+goal},
                            {"name","__tlsf_gr1_goal_counter_"+field(goal)},
                            {"goal",goal},{"reset",0},{"effective_initial",goal==0},
                            {"advance_to_goal",(goal+1)%ngoals}});
  }
  return O{{"format","tlsf-gr1-certificate-v1"},{"status","realizable"},
           {"side","system"},
           {"reduction_semantics",semantics==TLSF_GR1_EXACT?"exact":"strict"},
           {"circuit",O{{"path","memory"},{"kind","ASCII AIGER combinational"}}},
           {"fixpoint","generalized fixed-arity monitor certificate"},
           {"counts",O{{"goals",ngoals},{"justice_records",aig_num_justice(game)},
                        {"fairness_assumptions",target.fairness},{"state_variables",nstate},
                        {"original_game_latches",nstate},{"sampling_latches",0},
                        {"uncontrollable_inputs",nu},{"controllable_inputs",nc},
                        {"predicates",aig_num_outputs(certificate)},
                        {"aig_inputs",aig_num_inputs(certificate)},{"aig_latches",0},
                        {"aig_ands",aig_num_ands(certificate)},
                        {"levels_per_goal",depths}}},
           {"outputs",outputs},{"goals",goals},
           {"variables",O{{"state",state},{"uncontrollable",unc},{"controllable",con}}},
           {"sampling_semantics","No input-dependent acceptance sampling latches were required."},
           {"goal_counter_latches",counters},
           {"goal_counter_semantics","All-zero denotes goal 0; goals advance cyclically."},
           {"rank_semantics","y_j_k is definitionally the union of x_j_k_i."},
           {"move_semantics","Target transition relation and lifted invariant/ranks."},
           {"move_source","target_game"}};
}
std::unique_ptr<Aig,decltype(&aig_free)> emit_certificate(Schema &bdd,const GameView &target,
                          const LearnedCertificate &learned,const Config &cfg){
  const Aig *game=target.inst->r.game;
  auto out=std::unique_ptr<Aig,decltype(&aig_free)>(aig_new(),&aig_free);
  if(!out)throw Failure(TLSF_GR1_LIFT_LIMIT,"certificate_export","cannot allocate AIG");
  std::map<int,uint32_t> current,following;
  for(uint32_t p=0;p<target.states;p++)current[int(p)]=aig_input(out.get(),aig_latch_name(game,p));
  for(uint32_t p=0;p<target.inputs;p++)
    current[int(target.states+p)]=aig_input(out.get(),aig_input_name(game,p,nullptr));
  std::map<uint32_t,uint32_t> translated;
  for(uint32_t p=0;p<target.states;p++){
    uint32_t cur;aig_latch_at(game,p,&cur,nullptr,nullptr);translated[cur/2]=current[int(p)];
  }
  for(uint32_t p=0;p<target.inputs;p++){
    uint32_t lit;aig_input_name(game,p,&lit);translated[lit/2]=current[int(target.states+p)];
  }
  std::map<uint32_t,std::pair<uint32_t,uint32_t>> gates;
  for(uint32_t p=0;p<aig_num_ands(game);p++){
    uint32_t lhs,left,right;aig_and_at(game,p,&lhs,&left,&right);
    gates[lhs/2]={left,right};
  }
  std::function<uint32_t(uint32_t)> translate=[&](uint32_t lit)->uint32_t{
    cfg.check("certificate_export");
    if(lit<2)return lit;
    if(lit&1)return aig_not(translate(lit^1));
    auto it=translated.find(lit/2);if(it!=translated.end())return it->second;
    auto gate=gates.find(lit/2);
    if(gate==gates.end())decline("candidate","unmapped target game gate");
    uint32_t value=aig_and(out.get(),translate(gate->second.first),
                           translate(gate->second.second));
    translated.emplace(lit/2,value);return value;
  };
  for(uint32_t p=0;p<target.states;p++){
    uint32_t next;aig_latch_at(game,p,nullptr,&next,nullptr);
    following[int(p)]=translate(next);
  }
  for(uint32_t p=0;p<target.inputs;p++)following[int(target.states+p)]=current[int(target.states+p)];
  uint32_t bad=0;
  for(uint32_t p=0;p<aig_num_bad(game);p++){
    uint32_t lit;aig_bad_at(game,p,&lit);bad=aig_or(out.get(),bad,translate(lit));
  }
  auto predicate=[&](const std::string &name)->const B&{return learned.predicates.at(name);};
  auto now=[&](const B &b){return bdd.to_aig(out.get(),b,current);};
  auto later=[&](const B &b){return bdd.to_aig(out.get(),b,following);};
  auto inv=predicate("inv");
  aig_set_output(out.get(),"inv",now(inv));
  for(const Goal &g:target.goals){
    std::string name="goal_"+field(g.number);
    aig_set_output(out.get(),name.c_str(),now(predicate(name)));
  }
  for(const Goal &g:target.goals)
    for(int level=0;level<learned.depths[g.number];level++){
      std::string name="y_"+field(g.number)+"_"+field(level);
      aig_set_output(out.get(),name.c_str(),now(predicate(name)));
    }
  for(const Goal &g:target.goals)
    for(int level=0;level<learned.depths[g.number];level++)
      for(uint32_t fair=0;fair<std::max(1u,target.fairness);fair++){
        std::string name="x_"+field(g.number)+"_"+field(level)+"_"+field(fair);
        aig_set_output(out.get(),name.c_str(),now(predicate(name)));
      }
  std::vector<B> fairness;
  for(uint32_t fair=0;fair<target.fairness;fair++)
    fairness.push_back(bdd.from_aig(game,aig_fairness_at(game,fair),true));
  for(const Goal &g:target.goals){
    B at_goal=bdd.land(inv,predicate("goal_"+field(g.number)));
    uint32_t move=aig_and(out.get(),now(at_goal),
                          aig_and(out.get(),aig_not(bad),later(inv)));
    B covered=at_goal;
    for(int level=0;level<learned.depths[g.number];level++){
      B strict=level==0?at_goal:bdd.lor(at_goal,predicate("y_"+field(g.number)+"_"+field(level-1)));
      for(uint32_t fair=0;fair<std::max(1u,target.fairness);fair++){
        const B &x=predicate("x_"+field(g.number)+"_"+field(level)+"_"+field(fair));
        B fair_pred=fairness.empty()?bdd.t():fairness[fair];
        B rank_target=bdd.lor(strict,bdd.land(bdd.neg(fair_pred),x));
        B layer=bdd.land(x,bdd.neg(covered));
        move=aig_or(out.get(),move,aig_and(out.get(),now(layer),
                  aig_and(out.get(),aig_not(bad),later(rank_target))));
        covered=bdd.lor(covered,x);
      }
    }
    std::string name="move_"+field(g.number);
    aig_set_output(out.get(),name.c_str(),move);
  }
  return out;
}
J policy_sidecar(const GameView &target,const Aig *policy,
                 TlsfGr1ReductionSemantics semantics){
  const Aig *game=target.inst->r.game;
  uint32_t nstate=target.states,ngoals=uint32_t(target.goals.size());
  A state,counter,unc,con,advance;
  uint32_t uindex=0,cindex=0;
  for(uint32_t p=0;p<nstate;p++)
    state.emplace_back(O{{"policy_input",p},{"game_latch",p},
                         {"name",aig_latch_name(game,p)}});
  for(uint32_t goal=0;goal<ngoals;goal++){
    counter.emplace_back(O{{"policy_input",nstate+goal},{"goal",goal},
                           {"name","curr_"+field(goal)},{"reset",0},
                           {"effective_initial",goal==0}});
    advance.emplace_back(O{{"policy_output",0},{"goal",goal},
                           {"name","curr_next_"+field(goal)}});
  }
  for(uint32_t p=0;p<target.inputs;p++){
    const char *name=aig_input_name(game,p,nullptr);
    if(target.controls[p])
      con.emplace_back(O{{"policy_output",cindex++},{"game_input",p},{"name",name}});
    else
      unc.emplace_back(O{{"policy_input",nstate+ngoals+uindex++},
                         {"game_input",p},{"name",name}});
  }
  for(uint32_t p=0;p<ngoals;p++)advance[p].as_object()["policy_output"]=cindex+p;
  return O{{"format","tlsf-gr1-policy-v1"},{"side","system"},
           {"reduction_semantics",semantics==TLSF_GR1_EXACT?"exact":"strict"},
           {"circuit",O{{"path","memory"},{"kind","ASCII AIGER combinational"}}},
           {"counts",O{{"game_state_variables",nstate},{"original_game_latches",nstate},
                        {"sampling_latches",0},{"goals",ngoals},
                        {"uncontrollable_inputs",uindex},{"controllable_outputs",cindex},
                        {"aig_inputs",aig_num_inputs(policy)},
                        {"aig_outputs",aig_num_outputs(policy)},
                        {"aig_ands",aig_num_ands(policy)}}},
           {"inputs",O{{"state",state},{"counter",counter},{"uncontrollable",unc}}},
           {"outputs",O{{"controllable",con},{"counter_next",advance}}},
           {"counter_semantics","All-zero denotes curr_0; advance on the current goal."},
           {"skolem_rule","controllable inputs in game order, true/lowest index first"}};
}
std::unique_ptr<Aig,decltype(&aig_free)> emit_policy(Schema &bdd,const GameView &target,
                     const Aig *certificate,const Config &cfg){
  const Aig *game=target.inst->r.game;
  uint32_t nstate=target.states,ngoals=uint32_t(target.goals.size());
  uint32_t public_width=nstate+target.inputs;
  int start=bdd.width();bdd.grow(start+int(ngoals)+int(public_width));
  std::map<int,int> public_to_policy;
  for(uint32_t p=0;p<public_width;p++)public_to_policy[int(p)]=start+int(ngoals+p);
  std::vector<B> moves,goals,curr,effective;
  for(uint32_t goal=0;goal<ngoals;goal++){
    std::string move="move_"+field(goal),g="goal_"+field(goal);
    moves.push_back(bdd.relabel(bdd.from_aig(certificate,aig_output_lit(certificate,move.c_str())),
                                public_to_policy));
    goals.push_back(bdd.relabel(bdd.from_aig(certificate,aig_output_lit(certificate,g.c_str())),
                                public_to_policy));
    curr.push_back(bdd.var(start+int(goal)));
  }
  B any=bdd.f();for(const B &b:curr)any=bdd.lor(any,b);
  for(uint32_t goal=0;goal<ngoals;goal++)
    effective.push_back(goal==0?bdd.lor(curr[0],bdd.neg(any)):curr[goal]);
  B relation=bdd.f();
  for(uint32_t goal=0;goal<ngoals;goal++)
    relation=bdd.lor(relation,bdd.land(effective[goal],moves[goal]));
  std::vector<int> controls;
  std::vector<std::string> control_names;
  for(uint32_t p=0;p<target.inputs;p++){
    const char *name=aig_input_name(game,p,nullptr);
    if(target.controls[p]){
      controls.push_back(public_to_policy.at(int(nstate+p)));
      control_names.emplace_back(name);
    }
  }
  B control_cube=bdd.cube({controls.begin(),controls.end()});
  B chosen=bdd.t();
  std::vector<B> functions;
  for(int control:controls){
    cfg.check("policy");
    B bit=bdd.var(control);
    B function=bdd.exists(bdd.land(bdd.land(relation,chosen),bit),control_cube);
    functions.push_back(function);
    chosen=bdd.land(chosen,bdd.lor(bdd.land(bit,function),
                      bdd.land(bdd.neg(bit),bdd.neg(function))));
  }
  std::vector<B> next_curr;
  for(uint32_t goal=0;goal<ngoals;goal++){
    B advance=bdd.land(effective[goal],goals[goal]);
    uint32_t previous=(goal+ngoals-1)%ngoals;
    next_curr.push_back(bdd.lor(bdd.land(effective[goal],bdd.neg(advance)),
                      bdd.land(effective[previous],goals[previous])));
  }
  auto policy=std::unique_ptr<Aig,decltype(&aig_free)>(aig_new(),&aig_free);
  if(!policy)throw Failure(TLSF_GR1_LIFT_LIMIT,"policy","cannot allocate AIG");
  std::map<int,uint32_t> mapping;
  for(uint32_t p=0;p<nstate;p++)
    mapping[public_to_policy.at(int(p))]=aig_input(policy.get(),aig_latch_name(game,p));
  for(uint32_t goal=0;goal<ngoals;goal++){
    std::string name="curr_"+field(goal);
    mapping[start+int(goal)]=aig_input(policy.get(),name.c_str());
  }
  for(uint32_t p=0;p<target.inputs;p++){
    const char *name=aig_input_name(game,p,nullptr);
    if(!target.controls[p])
      mapping[public_to_policy.at(int(nstate+p))]=aig_input(policy.get(),name);
  }
  for(size_t p=0;p<controls.size();p++)
    aig_set_output(policy.get(),control_names[p].c_str(),
                   bdd.to_aig(policy.get(),functions[p],mapping));
  for(uint32_t goal=0;goal<ngoals;goal++){
    std::string name="curr_next_"+field(goal);
    aig_set_output(policy.get(),name.c_str(),
                   bdd.to_aig(policy.get(),next_curr[goal],mapping));
  }
  return policy;
}
TlsfGr1CheckResult check(const Candidate &candidate,const Config &cfg,
                         TlsfGr1CheckMethod method,uint64_t deadline){
  TlsfGr1CheckInput input{};
  input.game_aag={(const uint8_t *)candidate.game.data(),candidate.game.size()};
  input.certificate_aag={(const uint8_t *)candidate.certificate.data(),candidate.certificate.size()};
  input.certificate_json={(const uint8_t *)candidate.certificate_json.data(),candidate.certificate_json.size()};
  if(method==TLSF_GR1_CHECK_CERTIFICATE){
    input.policy_aag={(const uint8_t *)candidate.policy.data(),candidate.policy.size()};
    input.policy_json={(const uint8_t *)candidate.policy_json.data(),candidate.policy_json.size()};
  }
  TlsfGr1CheckOptions options{};
  options.method = method;
  options.node_cap=cfg.o.checker_nodes;options.cache_cap=cfg.o.checker_cache;
  options.max_artifact_bytes=cfg.o.max_artifact_bytes;
  options.deadline_mono_ns=deadline;
  options.cancelled=cfg.o.cancelled;options.cancel_ctx=cfg.o.cancel_ctx;
  TlsfGr1CheckResult result{};
  tlsf_gr1_check(&input,&options,&result);
  return result;
}
Candidate prove(Schema &bdd,const GameView &target,const LearnedCertificate &learned,
                TlsfGr1ReductionSemantics semantics,const Config &cfg){
  Candidate candidate;
  candidate.game.assign(target.inst->r.aag,target.inst->r.aag_size);
  auto cert=emit_certificate(bdd,target,learned,cfg);
  candidate.certificate=render_aig(cert.get(),cfg);
  candidate.certificate_json=dump(certificate_sidecar(target,learned,cert.get(),semantics));
  cfg.bytes(candidate.certificate_json.size(),"certificate_export");
  cfg.check("policy");
  uint64_t proof_deadline=cfg.o.deadline_mono_ns;
  if(proof_deadline){
    uint64_t now=now_ns();
    if(now>=proof_deadline)
      throw Failure(TLSF_GR1_LIFT_DEADLINE,"policy","deadline exceeded");
    proof_deadline=now+uint64_t(double(proof_deadline-now)*cfg.o.policy_proof_fraction);
  }
  Config policy_cfg=cfg;policy_cfg.o.deadline_mono_ns=proof_deadline;
  bool capacity_fallback=false;
  try {
    bdd.set_config(policy_cfg);
    auto policy=emit_policy(bdd,target,cert.get(),policy_cfg);
    candidate.policy=render_aig(policy.get(),policy_cfg);
    candidate.policy_json=dump(policy_sidecar(target,policy.get(),semantics));
    policy_cfg.bytes(candidate.policy_json.size(),"policy");
    auto result=check(candidate,policy_cfg,TLSF_GR1_CHECK_CERTIFICATE,proof_deadline);
    if(result.status==TLSF_GR1_CHECK_CANCELLED){
      tlsf_gr1_check_result_clear(&result);
      throw Failure(TLSF_GR1_LIFT_CANCELLED,"target_check","checker cancelled");
    }
    if(result.status==TLSF_GR1_CHECK_OK && result.verdict==TLSF_GR1_CHECK_VERIFIED){
      candidate.method=TLSF_GR1_CHECK_CERTIFICATE;
      candidate.verdict=result.verdict;
      if(result.json)candidate.check_json.assign(result.json,result.json_size);
      tlsf_gr1_check_result_clear(&result);
      bdd.set_config(cfg);
      return candidate;
    }
    capacity_fallback=result.status==TLSF_GR1_CHECK_LIMIT ||
                      result.status==TLSF_GR1_CHECK_DEADLINE;
    tlsf_gr1_check_result_clear(&result);
    if(!capacity_fallback)decline("target_check","certificate not verified");
  } catch(const Failure &e){
    bdd.set_config(cfg);
    if(e.status==TLSF_GR1_LIFT_LIMIT || e.status==TLSF_GR1_LIFT_DEADLINE)
      capacity_fallback=true;
    else throw;
  }
  bdd.set_config(cfg);
  if(!capacity_fallback)decline("target_check","policy check failed");
  cfg.check("region_check");
  auto region=check(candidate,cfg,TLSF_GR1_CHECK_REGION,cfg.o.deadline_mono_ns);
  if(region.status==TLSF_GR1_CHECK_CANCELLED ||
     region.status==TLSF_GR1_CHECK_DEADLINE ||
     region.status==TLSF_GR1_CHECK_LIMIT){
    auto status=region.status;
    tlsf_gr1_check_result_clear(&region);
    throw Failure(status==TLSF_GR1_CHECK_CANCELLED?TLSF_GR1_LIFT_CANCELLED:
                  status==TLSF_GR1_CHECK_DEADLINE?TLSF_GR1_LIFT_DEADLINE:
                  TLSF_GR1_LIFT_LIMIT,"region_check","checker capacity or deadline");
  }
  if(region.status==TLSF_GR1_CHECK_OK &&
     region.verdict==TLSF_GR1_CHECK_REGION_VERIFIED){
    candidate.method=TLSF_GR1_CHECK_REGION;
    candidate.verdict=region.verdict;
    if(region.json)candidate.check_json.assign(region.json,region.json_size);
    candidate.policy.clear();candidate.policy_json.clear();
    tlsf_gr1_check_result_clear(&region);
    return candidate;
  }
  tlsf_gr1_check_result_clear(&region);
  decline("target_check","region not verified");
}
char *copy_bytes(const std::string &value){
  char *p=(char *)malloc(value.size()+1);
  if(!p)throw Failure(TLSF_GR1_LIFT_LIMIT,"publish","cannot allocate result");
  memcpy(p,value.data(),value.size());p[value.size()]='\0';return p;
}
TlsfGr1LiftOptions defaults(const TlsfGr1LiftOptions *provided){
  TlsfGr1LiftOptions out{};
  if(provided)out=*provided;
  if(!out.solver_nodes)out.solver_nodes=TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES;
  if(!out.solver_cache)out.solver_cache=TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE;
  if(!out.checker_nodes)out.checker_nodes=TLSF_GR1_LIFT_DEFAULT_CHECKER_NODES;
  if(!out.checker_cache)out.checker_cache=TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE;
  if(!out.schema_nodes)out.schema_nodes=TLSF_GR1_LIFT_DEFAULT_SCHEMA_NODES;
  if(!out.schema_cache)out.schema_cache=TLSF_GR1_LIFT_DEFAULT_SCHEMA_CACHE;
  if(!out.max_artifact_bytes)out.max_artifact_bytes=TLSF_GR1_LIFT_DEFAULT_MAX_ARTIFACT_BYTES;
  if(!out.max_monitor_states)out.max_monitor_states=TLSF_GR1_LIFT_DEFAULT_MAX_MONITOR_STATES;
  if(!out.max_sizes_per_axis)out.max_sizes_per_axis=TLSF_GR1_LIFT_DEFAULT_MAX_SIZES_PER_AXIS;
  if(!out.max_predicate_arity)out.max_predicate_arity=TLSF_GR1_LIFT_DEFAULT_MAX_PREDICATE_ARITY;
  if(!out.max_subsets_per_predicate)
    out.max_subsets_per_predicate=TLSF_GR1_LIFT_DEFAULT_MAX_SUBSETS_PER_PREDICATE;
  if(!out.policy_proof_fraction)
    out.policy_proof_fraction=TLSF_GR1_LIFT_DEFAULT_POLICY_PROOF_FRACTION;
  if(!out.discovery_share)out.discovery_share=TLSF_GR1_LIFT_DEFAULT_DISCOVERY_SHARE;
  return out;
}
void run(const uint8_t *source,size_t size,
         const std::map<std::string,int64_t> &target_overrides,
         const Config &cfg,TlsfGr1LiftResult &result){
  uint64_t started=now_ns();
  cfg.check("source");
  char source_hash[65]{};
  if(!tlsf_pipeline_source_sha256(source,size,source_hash))
    throw Failure(TLSF_GR1_LIFT_INVALID,"source","invalid byte snapshot or embedded NUL");
  int declared_parameters=tlsf_source_parameter_count(source,size);
  if (declared_parameters<0) decline("parse","source parse failed");
  if (declared_parameters==0) decline("parameters","absent");
  TlsfGr1ReductionSemantics semantics=TLSF_GR1_EXACT;
  std::unique_ptr<Instance> target;
  try {target=lower(source,size,target_overrides,semantics,cfg);}
  catch(const Failure &e){
    if(e.status!=TLSF_GR1_LIFT_DECLINED && e.status!=TLSF_GR1_LIFT_UNSUPPORTED)throw;
    semantics=TLSF_GR1_STRICT;
    target=lower(source,size,target_overrides,semantics,cfg);
  }
  auto axes=parameters(*target);
  if(axes.empty())decline("parameters","absent");
  Config discovery_cfg=cfg;
  if(cfg.o.deadline_mono_ns){
    cfg.check("seed_window");
    uint64_t elapsed_budget=cfg.o.deadline_mono_ns-started;
    discovery_cfg.o.deadline_mono_ns=std::min(cfg.o.deadline_mono_ns,
      started+uint64_t(double(elapsed_budget)*cfg.o.discovery_share));
  }
  auto window=discover(source,size,*target,semantics,discovery_cfg);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (lift_test_fault==1 && !window.sizes.empty()) window.sizes[0]++;
#endif
  validate_window(window,*target);
  for(auto &seed:window.seeds)solve_seed(*seed,discovery_cfg);
  std::vector<GameView> seeds;
  seeds.reserve(window.seeds.size());
  for(auto &seed:window.seeds)seeds.emplace_back(*seed,window.modes,discovery_cfg);
  GameView target_view(*target,window.modes,discovery_cfg);
  uint32_t width=uint32_t(target_view.variables.size());
  for(const auto &seed:seeds)width=std::max(width,uint32_t(seed.variables.size()));
  Schema bdd(discovery_cfg,width);
  auto learned=learn_certificate(bdd,seeds,target_view,discovery_cfg);
  bdd.set_config(cfg);
  Candidate candidate=prove(bdd,target_view,learned,semantics,cfg);
  if(candidate.verdict!=TLSF_GR1_CHECK_VERIFIED &&
     candidate.verdict!=TLSF_GR1_CHECK_REGION_VERIFIED)
    decline("target_check","unverified candidate");
  cfg.check("publish");
  cfg.bytes(candidate.game.size(),"publish");
  cfg.bytes(candidate.certificate.size(),"publish");
  cfg.bytes(candidate.certificate_json.size(),"publish");
  cfg.bytes(candidate.policy.size(),"publish");
  cfg.bytes(candidate.policy_json.size(),"publish");
  cfg.bytes(candidate.check_json.size(),"publish");
  char game_hash[65]{},cert_hash[65]{},policy_hash[65]{};
  if(!tlsf_pipeline_source_sha256(candidate.game.data(),candidate.game.size(),game_hash) ||
     !tlsf_pipeline_source_sha256(candidate.certificate.data(),candidate.certificate.size(),cert_hash))
    throw Failure(TLSF_GR1_LIFT_ERROR,"publish","artifact hash failed");
  if(candidate.method==TLSF_GR1_CHECK_CERTIFICATE &&
     (candidate.policy.empty() ||
      !tlsf_pipeline_source_sha256(candidate.policy.data(),candidate.policy.size(),policy_hash)))
    throw Failure(TLSF_GR1_LIFT_ERROR,"publish","policy artifact hash failed");
  A values,roles;
  for(int v:window.sizes)values.emplace_back(v);
  for(const auto &[index,role]:target_view.roles)
    roles.emplace_back(O{{"index",index},{"signature",role}});
  O arities;
  for(const auto &[name,arity]:learned.arities)arities[name]=arity;
  J evidence=O{{"format",TLSF_GR1_LIFT_EVIDENCE_FORMAT},
               {"source_sha256",source_hash},{"game_sha256",game_hash},
               {"certificate_sha256",cert_hash},{"axis",window.axis},
               {"seed_values",values},{"roles",roles},{"predicate_arities",arities},
               {"move_source","target_transition"},
               {"reduction_semantics",semantics==TLSF_GR1_EXACT?"exact":"strict"},
               {"method",candidate.method==TLSF_GR1_CHECK_REGION?"gr1-region-v1":"certificate"},
               {"verdict",candidate.method==TLSF_GR1_CHECK_REGION?"REGION_VERIFIED":"VERIFIED"},
               {"global_knobs",O{{"max_sizes_per_axis",cfg.o.max_sizes_per_axis},
                                   {"max_predicate_arity",cfg.o.max_predicate_arity},
                                   {"max_subsets_per_predicate",cfg.o.max_subsets_per_predicate},
                                   {"seed_confirmation",cfg.o.seed_confirmation!=2},
                                   {"policy_proof_fraction",cfg.o.policy_proof_fraction},
                                   {"discovery_share",cfg.o.discovery_share},
                                   {"solver_nodes",cfg.o.solver_nodes},
                                   {"solver_cache",cfg.o.solver_cache},
                                   {"checker_nodes",cfg.o.checker_nodes},
                                   {"checker_cache",cfg.o.checker_cache},
                                   {"schema_nodes",cfg.o.schema_nodes},
                                   {"schema_cache",cfg.o.schema_cache}}}};
  if(candidate.method==TLSF_GR1_CHECK_CERTIFICATE)
    evidence.as_object()["policy_sha256"]=policy_hash;
  candidate.evidence=dump(evidence);
  cfg.bytes(candidate.evidence.size(),"publish");
  result.game_size=candidate.game.size();result.game_aag=copy_bytes(candidate.game);
  result.certificate_size=candidate.certificate.size();result.certificate_aag=copy_bytes(candidate.certificate);
  result.certificate_json_size=candidate.certificate_json.size();
  result.certificate_json=copy_bytes(candidate.certificate_json);
  result.policy_size=candidate.policy.size();
  if(!candidate.policy.empty())result.policy_aag=copy_bytes(candidate.policy);
  result.policy_json_size=candidate.policy_json.size();
  if(!candidate.policy_json.empty())result.policy_json=copy_bytes(candidate.policy_json);
  result.check_json_size=candidate.check_json.size();result.check_json=copy_bytes(candidate.check_json);
  result.evidence_size=candidate.evidence.size();result.evidence_json=copy_bytes(candidate.evidence);
  result.semantics=semantics;result.method=candidate.method;result.verdict=candidate.verdict;
}
} // namespace

#ifdef TLSF_GR1_LIFT_TEST_FAULT
/* Compiled only into native_lift_api, never into the installed library. */
extern "C" void tlsf_gr1_lift_test_set_fault(int fault) {
  lift_test_fault=fault;
}
#endif

extern "C" void tlsf_gr1_lift_result_clear(TlsfGr1LiftResult *result){
  if(!result)return;
  free(result->game_aag);free(result->certificate_aag);free(result->certificate_json);
  free(result->policy_aag);free(result->policy_json);free(result->check_json);
  free(result->evidence_json);memset(result,0,sizeof *result);
}
extern "C" TlsfGr1LiftStatus
tlsf_gr1_lift(const uint8_t *source, size_t source_size,
              const ParamOverride *target_overrides,
              size_t target_override_count, const TlsfGr1LiftOptions *options,
              TlsfGr1LiftResult *result, TlsfGr1LiftError *error) {
  if(error)memset(error,0,sizeof *error);
  if (!result || !source || !source_size ||
      (target_override_count && !target_overrides)) {
    if(error){error->status=TLSF_GR1_LIFT_INVALID;
      snprintf(error->stage,sizeof error->stage,"arguments");
      snprintf(error->message, sizeof error->message, "invalid arguments");
    }
    return TLSF_GR1_LIFT_INVALID;
  }
  if(result->game_aag || result->certificate_aag || result->certificate_json ||
     result->policy_aag || result->policy_json || result->check_json || result->evidence_json){
    if(error){error->status=TLSF_GR1_LIFT_INVALID;
      snprintf(error->stage,sizeof error->stage,"arguments");
      snprintf(error->message,sizeof error->message,"result must be empty");}
    return TLSF_GR1_LIFT_INVALID;
  }
  memset(result,0,sizeof *result);
  try {
    Config cfg{defaults(options)};
    if(!std::isfinite(cfg.o.policy_proof_fraction) ||
       cfg.o.policy_proof_fraction<=0 || cfg.o.policy_proof_fraction>1 ||
       !std::isfinite(cfg.o.discovery_share) || cfg.o.discovery_share<=0 ||
       cfg.o.discovery_share>1)
      throw Failure(TLSF_GR1_LIFT_INVALID,"options","invalid deadline fractions");
    std::map<std::string,int64_t> overrides;
    for(size_t p=0;p<target_override_count;p++){
      const ParamOverride &row=target_overrides[p];
      if(!row.name || !*row.name || !overrides.emplace(row.name,row.value).second)
        throw Failure(TLSF_GR1_LIFT_INVALID,"override","empty or duplicate target override");
    }
    cfg.bytes(source_size,"source");
    std::string snapshot(reinterpret_cast<const char *>(source),source_size);
    run(reinterpret_cast<const uint8_t *>(snapshot.data()),snapshot.size(),
        overrides,cfg,*result);
    if(error)error->status=TLSF_GR1_LIFT_OK;
    return TLSF_GR1_LIFT_OK;
  } catch(const Failure &e){
    tlsf_gr1_lift_result_clear(result);
    if(error){error->status=e.status;
      snprintf(error->stage,sizeof error->stage,"%s",e.stage.c_str());
      snprintf(error->message,sizeof error->message,"%s",e.what());}
    return e.status;
  } catch(const std::bad_alloc &){
    tlsf_gr1_lift_result_clear(result);
    if(error){error->status=TLSF_GR1_LIFT_LIMIT;
      snprintf(error->stage,sizeof error->stage,"allocation");
      snprintf(error->message,sizeof error->message,"host allocation failed");}
    return TLSF_GR1_LIFT_LIMIT;
  } catch(const std::exception &e){
    tlsf_gr1_lift_result_clear(result);
    if(error){error->status=TLSF_GR1_LIFT_ERROR;
      snprintf(error->stage,sizeof error->stage,"internal");
      snprintf(error->message,sizeof error->message,"%s",e.what());}
    return TLSF_GR1_LIFT_ERROR;
  } catch(...){
    tlsf_gr1_lift_result_clear(result);
    if(error){error->status=TLSF_GR1_LIFT_ERROR;
      snprintf(error->stage,sizeof error->stage,"internal");
      snprintf(error->message,sizeof error->message,"unknown exception");}
    return TLSF_GR1_LIFT_ERROR;
  }
}
