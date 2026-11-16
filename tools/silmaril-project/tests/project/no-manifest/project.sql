-- silmaril.project-db.v0.1
CREATE TABLE meta(
  key TEXT NOT NULL PRIMARY KEY,
  value TEXT NOT NULL
);
CREATE TABLE projects(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  version TEXT,
  description TEXT,
  root TEXT,
  url TEXT,
  rev TEXT,
  UNIQUE(name)
);
CREATE TABLE objects(
  sid TEXT NOT NULL PRIMARY KEY,
  kind TEXT NOT NULL,
  name TEXT NOT NULL,
  project TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  sid_source TEXT NOT NULL CHECK(sid_source IN ('derived','override')),
  UNIQUE(kind, name)
);
CREATE TABLE artifacts(
  sid TEXT NOT NULL PRIMARY KEY,
  cid TEXT NOT NULL,
  type TEXT NOT NULL,
  name TEXT,
  size INTEGER,
  sha256 TEXT,
  git_sha1 TEXT,
  registry TEXT NOT NULL,
  doc TEXT,
  UNIQUE(cid)
);
CREATE TABLE artifact_paths(
  package TEXT NOT NULL,
  path TEXT NOT NULL,
  artifact TEXT NOT NULL,
  PRIMARY KEY(package, path)
);
CREATE TABLE facts(
  subject TEXT NOT NULL,
  at TEXT NOT NULL,
  property TEXT NOT NULL,
  value TEXT NOT NULL,
  checker TEXT NOT NULL,
  tier TEXT NOT NULL CHECK(tier IN ('kernel','compiled','tool','external')),
  PRIMARY KEY(subject, at, property, checker)
);
CREATE TABLE artifact_types(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE formats(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  input TEXT NOT NULL,
  value_type TEXT NOT NULL,
  base TEXT,
  printer INTEGER NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE format_defaults(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  format TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE format_laws(
  name TEXT NOT NULL PRIMARY KEY,
  format TEXT NOT NULL,
  law TEXT NOT NULL CHECK(law IN ('roundtrip','sound')),
  proof TEXT NOT NULL,
  rel TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE value_defs(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  format TEXT NOT NULL,
  decl TEXT NOT NULL,
  parses TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE value_sources(
  value TEXT NOT NULL,
  pos INTEGER NOT NULL,
  cid TEXT NOT NULL,
  format TEXT NOT NULL,
  decl TEXT NOT NULL,
  obligation TEXT NOT NULL,
  PRIMARY KEY(value, pos)
);
CREATE TABLE specs(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  model TEXT,
  format TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE models(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE rooms(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  sen TEXT NOT NULL,
  mod TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE machines(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  deterministic INTEGER NOT NULL,
  n_states INTEGER NOT NULL,
  n_labels INTEGER NOT NULL,
  n_edges INTEGER NOT NULL,
  canonical TEXT NOT NULL,
  dominators TEXT,
  dominator_theorem TEXT,
  UNIQUE(name)
);
CREATE TABLE machine_bindings(
  name TEXT NOT NULL PRIMARY KEY,
  machine TEXT NOT NULL,
  decl TEXT NOT NULL,
  marks TEXT,
  theorem TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT
);
CREATE TABLE language_domains(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  carrier TEXT NOT NULL,
  monoid INTEGER NOT NULL,
  letters TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE measures(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  decl TEXT NOT NULL,
  codomain TEXT NOT NULL,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE language_interpretations(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  decl TEXT NOT NULL,
  input TEXT NOT NULL,
  carrier TEXT NOT NULL,
  abi TEXT,
  environment TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE languages(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  op TEXT NOT NULL CHECK(op IN ('decl','format','artifact','union','inter','diff','regex','within')),
  decl TEXT NOT NULL,
  carrier TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  format TEXT,
  value TEXT,
  interpretation TEXT,
  regex TEXT,
  semantics TEXT CHECK(semantics IN ('list','monoid')),
  measure TEXT,
  bound INTEGER,
  term TEXT,
  identity TEXT NOT NULL,
  identity_hash TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE language_operands(
  language TEXT NOT NULL,
  pos INTEGER NOT NULL,
  operand TEXT NOT NULL,
  PRIMARY KEY(language, pos)
);
CREATE TABLE language_shape_roles(
  shape TEXT NOT NULL,
  pos INTEGER NOT NULL,
  role TEXT NOT NULL,
  PRIMARY KEY(shape, pos)
);
CREATE TABLE consequence_interpretations(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  input TEXT NOT NULL,
  contexts TEXT NOT NULL,
  conclusions TEXT NOT NULL,
  abi TEXT,
  environment TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE consequence_systems(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  op TEXT NOT NULL CHECK(op IN ('decl','union','inter','diff','erase','artifact')),
  decl TEXT NOT NULL,
  term TEXT NOT NULL,
  contexts TEXT NOT NULL,
  conclusions TEXT NOT NULL,
  witness TEXT,
  value TEXT,
  interpretation TEXT,
  ctx_kind TEXT CHECK(ctx_kind IN ('unit','list','finset','set','other')),
  ctx_elem TEXT,
  ctx_signed INTEGER,
  concl_kind TEXT CHECK(concl_kind IN ('unit','list','finset','set','other')),
  concl_elem TEXT,
  concl_signed INTEGER,
  raw_sequent INTEGER,
  title TEXT,
  doc TEXT,
  source TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE consequence_operands(
  system TEXT NOT NULL,
  pos INTEGER NOT NULL,
  operand TEXT NOT NULL,
  PRIMARY KEY(system, pos)
);
CREATE TABLE consequence_shape_roles(
  shape TEXT NOT NULL,
  pos INTEGER NOT NULL,
  role TEXT NOT NULL,
  PRIMARY KEY(shape, pos)
);
CREATE TABLE problems(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('prop','group')),
  decl TEXT,
  arity INTEGER,
  room TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  model TEXT,
  spec TEXT,
  expect TEXT,
  detached INTEGER NOT NULL,
  detached_reason TEXT,
  title TEXT,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE problem_args(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  name TEXT,
  type TEXT NOT NULL,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE problem_inputs(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  value TEXT,
  cid TEXT,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE instance_args(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  term TEXT,
  value TEXT,
  cid TEXT,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE answers(
  decl TEXT NOT NULL PRIMARY KEY,
  problem TEXT NOT NULL,
  status TEXT NOT NULL CHECK(status IN ('THM','SAT','UNS','CSA')),
  source TEXT NOT NULL CHECK(source IN ('answers','solves','refutes')),
  witness TEXT,
  module TEXT NOT NULL,
  tier TEXT NOT NULL
);
CREATE TABLE answer_axioms(
  decl TEXT NOT NULL,
  axiom TEXT NOT NULL,
  PRIMARY KEY(decl, axiom)
);
CREATE TABLE edges(
  record_kind TEXT NOT NULL,
  record_name TEXT NOT NULL,
  pos INTEGER NOT NULL,
  parent TEXT NOT NULL,
  child TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('sub','refute','instance')),
  via TEXT,
  PRIMARY KEY(record_kind, record_name, pos)
);
CREATE TABLE szs(
  code TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  verdict TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown'))
);
CREATE TABLE statuses(
  problem TEXT NOT NULL,
  status TEXT NOT NULL,
  via_kind TEXT NOT NULL,
  via TEXT NOT NULL,
  tier TEXT NOT NULL,
  PRIMARY KEY(problem, status)
);
CREATE TABLE summary(
  problem TEXT NOT NULL PRIMARY KEY,
  summary TEXT NOT NULL,
  verdict TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown')),
  tier TEXT NOT NULL
);
CREATE TABLE deprecations(
  name TEXT NOT NULL PRIMARY KEY,
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language')),
  reason TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE deprecation_replacements(
  name TEXT NOT NULL,
  pos INTEGER NOT NULL,
  replacement TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language')),
  PRIMARY KEY(name, pos)
);
CREATE TABLE deprecated_problems(
  problem TEXT NOT NULL PRIMARY KEY,
  via_kind TEXT NOT NULL CHECK(via_kind IN ('self','spec','instance')),
  via TEXT NOT NULL
);
CREATE TABLE findings(
  problem TEXT NOT NULL PRIMARY KEY,
  classification TEXT NOT NULL CHECK(classification IN ('error','spec_bug','model_gap','unclear')),
  note TEXT,
  pointer TEXT,
  fixed_in TEXT,
  disclosure_status TEXT CHECK(disclosure_status IN ('private','reported','public')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE finding_versions(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  version TEXT NOT NULL,
  PRIMARY KEY(problem, pos)
);
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
CREATE VIEW language_problems AS SELECT i.problem AS problem, e.parent AS shape, r.role AS role, i.pos AS pos, l.name AS language, p.expect AS expect, p.title AS title, s.summary AS summary, s.verdict AS verdict FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' JOIN language_shape_roles r ON r.shape = e.parent AND r.pos = i.pos JOIN languages l ON l.term = i.term JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;
CREATE VIEW consequence_problems AS SELECT i.problem AS problem, e.parent AS shape, r.role AS role, i.pos AS pos, c.name AS system, p.expect AS expect, p.title AS title, s.summary AS summary, s.verdict AS verdict FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos JOIN consequence_systems c ON c.term = i.term JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;
CREATE VIEW genuine_errors AS SELECT f.problem, p.title, s.summary, f.note, f.pointer, (SELECT group_concat(v.version, ',') FROM (SELECT version FROM finding_versions WHERE problem = f.problem ORDER BY pos) v) AS affected_versions, f.fixed_in, f.disclosure_status, f.module, f.origin FROM findings f JOIN problems p ON p.name = f.problem LEFT JOIN summary s ON s.problem = f.problem WHERE f.classification = 'error';
CREATE VIEW model_gaps AS SELECT f.pointer, f.problem, p.title, f.note FROM findings f JOIN problems p ON p.name = f.problem WHERE f.classification = 'model_gap';
CREATE VIEW spec_bugs AS SELECT f.problem, d.via_kind, d.via, f.note, f.pointer FROM findings f LEFT JOIN deprecated_problems d ON d.problem = f.problem WHERE f.classification = 'spec_bug';
CREATE VIEW deprecated_with_replacements AS SELECT d.name, d.kind, d.reason, (SELECT group_concat(r.replacement, ',') FROM (SELECT replacement FROM deprecation_replacements WHERE name = d.name ORDER BY pos) r) AS superseded_by, d.module, d.origin FROM deprecations d;
CREATE VIEW unclassified_failures AS SELECT s.problem, s.summary FROM summary s WHERE s.verdict = 'fails' AND s.problem NOT IN (SELECT problem FROM findings) AND s.problem NOT IN (SELECT problem FROM deprecated_problems);
CREATE INDEX edges_parent ON edges(parent, child, kind, via);
CREATE INDEX edges_child ON edges(child, parent);
CREATE INDEX edges_kind ON edges(kind);
CREATE INDEX summary_verdict ON summary(verdict, summary);
CREATE INDEX objects_kind ON objects(kind);
CREATE INDEX problems_detached ON problems(detached, name);
CREATE INDEX answers_problem ON answers(problem);
CREATE INDEX problem_inputs_value ON problem_inputs(value);
CREATE INDEX problem_inputs_cid ON problem_inputs(cid);
CREATE INDEX instance_args_value ON instance_args(value);
CREATE INDEX instance_args_cid ON instance_args(cid);
CREATE INDEX value_sources_cid ON value_sources(cid);
CREATE INDEX value_sources_obligation ON value_sources(obligation);
CREATE INDEX value_sources_format ON value_sources(format);
CREATE INDEX value_defs_format ON value_defs(format);
CREATE INDEX formats_base ON formats(base);
CREATE INDEX format_laws_format ON format_laws(format);
CREATE INDEX format_defaults_format ON format_defaults(format);
CREATE INDEX artifact_paths_artifact ON artifact_paths(artifact);
CREATE INDEX findings_classification ON findings(classification, problem);
CREATE INDEX findings_pointer ON findings(pointer);
CREATE INDEX deprecated_problems_via ON deprecated_problems(via);
CREATE INDEX deprecation_replacements_replacement ON deprecation_replacements(replacement);
CREATE INDEX machine_bindings_machine ON machine_bindings(machine);
CREATE INDEX languages_domain ON languages(domain, name);
CREATE INDEX languages_decl ON languages(decl);
CREATE INDEX languages_term ON languages(term);
CREATE INDEX languages_identity ON languages(identity_hash);
CREATE INDEX language_operands_operand ON language_operands(operand);
CREATE INDEX consequence_systems_term ON consequence_systems(term);
CREATE INDEX consequence_systems_value ON consequence_systems(value);
CREATE INDEX consequence_operands_operand ON consequence_operands(operand);
CREATE INDEX instance_args_term ON instance_args(term);
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.1');
INSERT INTO meta(key, value) VALUES('modules', 'Lib');
INSERT INTO meta(key, value) VALUES('roots', 'Lib');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.1');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 2, 'mu');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 3, 'b');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 4, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bytes_member', 0, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bytes_member', 1, 'bytes');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 3, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 3, 'mu');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 4, 'b');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 5, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 2, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 3, 'x');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 5, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 4, 'mu');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 5, 'b');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 6, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 7, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 3, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 3, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 4, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 3, 'ff');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 1, 'rules');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 2, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 3, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 4, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 5, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 6, 'f');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 7, 'g');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 8, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 9, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 5, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 2, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 3, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 4, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 5, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 6, 'f');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 7, 'g');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 8, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 9, 'phi');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
