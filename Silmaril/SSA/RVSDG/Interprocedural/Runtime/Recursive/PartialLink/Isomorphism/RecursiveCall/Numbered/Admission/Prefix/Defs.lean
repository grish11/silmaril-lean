module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs

/-! Ordered admission over the exact results of a typed module link. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial (Primitives)
open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports importsL importsR exports : Ports (Ty V S)}
variable {past pastL pastR sigs sigsL sigsR : List (Ports (Ty V S))}

/-- Align the actual bindings in two modules in link order. The plan
chooses an initial paired φ seed, later φ and λ extensions, and bindings
to link without admitting their callable outputs. The types fix the shared
signatures for each extension. -/
inductive Plan (Op : Dialect.{u, v} (ValueSort V S) S) (importsL importsR exports : Ports (Ty V S)) :
    Bool → {pastL sigsL pastR sigsR : List (Ports (Ty V S))} →
    ModuleTerm Op importsL pastL sigsL exports → ModuleTerm Op importsR pastR sigsR exports → Type (max u v + 1) where
  | done {pastL pastR : List (Ports (Ty V S))} {left : Wires importsL pastL exports} {right : Wires importsR pastR exports} :
      Plan Op importsL importsR exports true (.ret left) (.ret right)
  | skipL {seeded : Bool} {pastL sigsL pastR sigsR : List (Ports (Ty V S))}
      {head : Ports (Ty V S)} {node : VertexTerm Op importsL pastL head}
      {rest : ModuleTerm Op importsL (pastL ++ [head]) sigsL exports} {right : ModuleTerm Op importsR pastR sigsR exports}
      (next : Plan Op importsL importsR exports seeded rest right) :
      Plan Op importsL importsR exports seeded (.bind node rest) right
  | skipR {seeded : Bool} {pastL sigsL pastR sigsR : List (Ports (Ty V S))}
      {head : Ports (Ty V S)} {node : VertexTerm Op importsR pastR head}
      {left : ModuleTerm Op importsL pastL sigsL exports} {rest : ModuleTerm Op importsR (pastR ++ [head]) sigsR exports}
      (next : Plan Op importsL importsR exports seeded left rest) :
      Plan Op importsL importsR exports seeded left (.bind node rest)
  | seed {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {membersL membersR : List (Function V S)}
      {left : PhiTerm Op importsL pastL membersL} {right : PhiTerm Op importsR pastR membersR}
      {restL : ModuleTerm Op importsL (pastL ++ [memberPorts membersL]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [memberPorts membersR]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports false (.bind (.phi left) restL) (.bind (.phi right) restR)
  /-- Extend the checked prefix with a paired later φ group. -/
  | phi {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {members : List (Function V S)}
      {left : PhiTerm Op importsL pastL members} {right : PhiTerm Op importsR pastR members}
      {restL : ModuleTerm Op importsL (pastL ++ [memberPorts members]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [memberPorts members]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.phi left) restL) (.bind (.phi right) restR)
  /-- Reuse a paired dispatch entry, indexed newest first among the seed and
fresh groups. Alias and skipped bindings do not add dispatch entries. -/
  | phiAlias {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {members : List (Function V S)}
      {left : PhiTerm Op importsL pastL members} {right : PhiTerm Op importsR pastR members}
      {restL : ModuleTerm Op importsL (pastL ++ [memberPorts members]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [memberPorts members]) sigsR exports}
      (prior : Nat) (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.phi left) restL) (.bind (.phi right) restR)
  | lambda {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {fn : Function V S}
      {left : LambdaTerm Op importsL pastL fn} {right : LambdaTerm Op importsR pastR fn}
      {restL : ModuleTerm Op importsL (pastL ++ [[fn.port]]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [[fn.port]]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.lambda left) restL) (.bind (.lambda right) restR)
  /-- Choose between a bilateral exact alias and checked fresh admission. -/
  | lambdaAuto {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {fn : Function V S}
      {left : LambdaTerm Op importsL pastL fn} {right : LambdaTerm Op importsR pastR fn}
      {restL : ModuleTerm Op importsL (pastL ++ [[fn.port]]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [[fn.port]]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.lambda left) restL) (.bind (.lambda right) restR)
  /-- Reuse an earlier paired λ, indexed from most recent to oldest. Alias rows do not add entries. -/
  | alias {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {fn : Function V S}
      {left : LambdaTerm Op importsL pastL fn} {right : LambdaTerm Op importsR pastR fn}
      {restL : ModuleTerm Op importsL (pastL ++ [[fn.port]]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [[fn.port]]) sigsR exports}
      (prior : Nat) (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.lambda left) restL) (.bind (.lambda right) restR)
  /-- Reuse the first earlier pair whose two exact value checks succeed. -/
  | aliasFirst {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {fn : Function V S}
      {left : LambdaTerm Op importsL pastL fn} {right : LambdaTerm Op importsR pastR fn}
      {restL : ModuleTerm Op importsL (pastL ++ [[fn.port]]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [[fn.port]]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.lambda left) restL) (.bind (.lambda right) restR)

abbrev Row (family : Family m) {ports : Ports (Ty V S)} (values : Tuple m.Val ports) :=
  ∀ {port : Ty V S} (p : Port ports port), Option (PLift (family (values.get p)))

def singletonRow {family : Family m} {port : Ty V S} {value : m.Val port}
    (known : family value) : Row family (.cons value .nil) := fun p => match p with
  | .head => some ⟨known⟩
  | .tail p => nomatch p

/-- The proof table is indexed by the linker locals it describes. Every
cell refers to the value at that exact typed output position. -/
def Table (family : Family m) : {past : List (Ports (Ty V S))} → Locals m.Val past → Type u
  | [], _ => PUnit
  | _ :: _, locals => Row family locals.1 × Table family locals.2

def Table.empty (family : Family m) : {past : List (Ports (Ty V S))} → (locals : Locals m.Val past) → Table family locals
  | [], _ => PUnit.unit
  | _ :: _, locals => ⟨fun _ => none, Table.empty family locals.2⟩

def Table.get {family : Family m} : {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} →
    Table family locals → (i : Fin past.length) → Row family (locals.get i)
  | [], _, _, i => i.elim0
  | head :: tail, locals, table, i => fun p =>
    (Fin.cases (motive := fun (j : Fin (head :: tail).length) => Row family (locals.get j))
      (fun {_t} p => table.1 p) (fun j {_t} p => Table.get table.2 j p) i) p

def Table.snoc {family : Family m} {ports : Ports (Ty V S)} {values : Tuple m.Val ports}
    (row : Row family values) : {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} →
    Table family locals → Table family (locals.snoc values)
  | [], _, _ => ⟨row, PUnit.unit⟩
  | _ :: _, _, table => ⟨table.1, Table.snoc row table.2⟩

def Table.lift {family target : Family m}
    (includeValue : ∀ {port : Ty V S} {value : m.Val port}, family value → target value) :
    {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} → Table family locals → Table target locals
  | [], _, _ => PUnit.unit
  | _ :: _, _, table => ⟨fun p => (table.1 p).map (fun cert => ⟨includeValue cert.down⟩), Table.lift includeValue table.2⟩

/-- Ordinary values are admitted at use. A nonordinary import has no
entry, while a callable output must have been admitted at its binding. -/
def Table.available {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (table : Table family locals)
    (ordinary : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → family value) :
    Available family entry locals :=
  fun {port} origin =>
    if plain : ordinaryPort port = true then some ⟨ordinary _ plain⟩
    else match origin with
      | .arg _ => none
      | .output row p => table.get row p

def memberRow {family : Family m} :
    (members : List (Function V S)) → (values : (i : Fin members.length) → m.Val members[i].port) →
    (∀ i, family (values i)) → Row family (memberValues members values)
  | [], _, _, _, p => nomatch p
  | _ :: _, _, known, _, .head => some ⟨known 0⟩
  | _ :: rest, values, known, _, .tail p => memberRow rest (fun i => values i.succ) (fun i => known i.succ) p

def exportWire {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (available : Available family entry locals) :
    {ports : Ports (Ty V S)} → (wires : Wires imports past ports) → {port : Ty V S} →
    (p : Port ports port) → Option (PLift (family ((wires.read entry locals).get p)))
  | [], .nil, _, p => nomatch p
  | _ :: _, .cons origin _, _, .head => available origin
  | _ :: _, .cons _ rest, _, .tail p => exportWire available rest p

variable {primitives : Primitives m σ} {ids : GlobalRel}

/-- Each recorded pair consists of the two actual linked values of one
previously admitted λ row. -/
structure LambdaEntry (familyL familyR : Family m) where
  fn : Function V S
  left : m.Val fn.port
  right : m.Val fn.port
  knownL : familyL left
  knownR : familyR right

def LambdaEntry.inherit {familyL familyR : Family m} {fn : Function V S}
    {calleeL calleeR : m.Val fn.port} (entry : LambdaEntry familyL familyR) :
    LambdaEntry (WithExport familyL calleeL) (WithExport familyR calleeR) :=
  ⟨entry.fn, entry.left, entry.right, .inherited entry.knownL, .inherited entry.knownR⟩

/-- Coalesce only when both new linked values equal the corresponding
values of the same earlier pair. Reuse its membership at the exact new values. -/
def LambdaEntry.checkAlias [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entry : LambdaEntry familyL familyR) (check : ExactValueCheck m) {fn : Function V S}
    (left right : m.Val fn.port) : Option (PLift (familyL left ∧ familyR right)) :=
  letI : DecidableEq (Function V S) := fun a b =>
    decidable_of_iff (a.args = b.args ∧ a.results = b.results) (by cases a; cases b; simp)
  if same : entry.fn = fn then
    match fn, same, left, right with
    | _, rfl, left, right => do
      let leftEq ← check left entry.left
      let rightEq ← check right entry.right
      pure ⟨leftEq.down.symm ▸ entry.knownL, rightEq.down.symm ▸ entry.knownR⟩
  else none

/-- A successful scan carries a bounded index in the supplied dispatch
list, its first-success proof and the membership evidence from that pair. -/
structure AliasMatch [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entries : List (LambdaEntry familyL familyR)) (check : ExactValueCheck m)
    {fn : Function V S} (left right : m.Val fn.port) where
  index : Fin entries.length
  first : entries.findIdx? (fun entry => (entry.checkAlias check (fn := fn) left right).isSome) = some index.val
  known : familyL left ∧ familyR right

def findAliasCandidate [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entries : List (LambdaEntry familyL familyR)) (check : ExactValueCheck m)
    {fn : Function V S} (left right : m.Val fn.port) : Option (Nat × PLift (familyL left ∧ familyR right)) :=
  entries.zipIdx.findSome? fun row =>
    (row.1.checkAlias check (fn := fn) left right).map fun known => (row.2, known)

theorem findAliasCandidate_index [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entries : List (LambdaEntry familyL familyR)) (check : ExactValueCheck m)
    {fn : Function V S} (left right : m.Val fn.port) :
    (findAliasCandidate entries check (fn := fn) left right).map Prod.fst =
      entries.findIdx? (fun entry => (entry.checkAlias check (fn := fn) left right).isSome) := by
  rw [findAliasCandidate, List.map_findSome?, List.findIdx?_eq_findSome?_zipIdx]
  congr 1
  funext row
  obtain ⟨entry, _⟩ := row
  cases checked : entry.checkAlias check (fn := fn) left right <;> simp [checked]

/-- Scan in the prefix's existing order, most recent first. Each candidate
uses the explicit alias check on one pair and retains its evidence. -/
def findAlias [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entries : List (LambdaEntry familyL familyR)) (check : ExactValueCheck m)
    {fn : Function V S} (left right : m.Val fn.port) :
    Option (AliasMatch entries check (fn := fn) left right) :=
  match found : findAliasCandidate entries check (fn := fn) left right with
  | none => none
  | some (index, known) =>
    have first := (findAliasCandidate_index entries check (fn := fn) left right).symm.trans (congrArg (Option.map Prod.fst) found)
    some ⟨⟨index, (List.findIdx?_eq_some_iff_findIdx_eq.mp first).1⟩, first, known.down⟩

theorem AliasMatch.accepted [DecidableEq (Ty V S)] {familyL familyR : Family m}
    {entries : List (LambdaEntry familyL familyR)} {check : ExactValueCheck m}
    {fn : Function V S} {left right : m.Val fn.port} (hit : AliasMatch entries check (fn := fn) left right) :
    (entries[hit.index].checkAlias check (fn := fn) left right).isSome = true :=
  (List.findIdx?_eq_some_iff_getElem.mp hit.first).choose_spec.1

theorem AliasMatch.noEarlier [DecidableEq (Ty V S)] {familyL familyR : Family m}
    {entries : List (LambdaEntry familyL familyR)} {check : ExactValueCheck m}
    {fn : Function V S} {left right : m.Val fn.port} (hit : AliasMatch entries check (fn := fn) left right)
    (i : Fin entries.length) (before : i < hit.index) :
    ¬(entries[i].checkAlias check (fn := fn) left right).isSome :=
  (List.findIdx?_eq_some_iff_getElem.mp hit.first).choose_spec.2 i before

/-- A miss means every paired check failed. The statement refers to the
supplied checker's results and requires no completeness of that checker. -/
theorem findAlias_none_iff [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entries : List (LambdaEntry familyL familyR)) (check : ExactValueCheck m)
    {fn : Function V S} (left right : m.Val fn.port) :
    findAlias entries check (fn := fn) left right = none ↔
      ∀ entry ∈ entries, (entry.checkAlias check (fn := fn) left right).isSome = false := by
  rw [← List.findIdx?_eq_none_iff, ← findAliasCandidate_index]
  unfold findAlias
  split <;> simp_all

/-- The paired dispatch entry records linked values and membership for every slot. -/
structure GroupEntry (familyL familyR : Family m) where
  membersL : List (Function V S)
  membersR : List (Function V S)
  left : Group m membersL
  right : Group m membersR
  knownL : ∀ slot, familyL (left.ref slot)
  knownR : ∀ slot, familyR (right.ref slot)

def GroupEntry.lift {familyL familyR targetL targetR : Family m}
    (includeL : ∀ {port : Ty V S} {value : m.Val port}, familyL value → targetL value)
    (includeR : ∀ {port : Ty V S} {value : m.Val port}, familyR value → targetR value)
    (entry : GroupEntry familyL familyR) : GroupEntry targetL targetR :=
  ⟨entry.membersL, entry.membersR, entry.left, entry.right,
    fun slot => includeL (entry.knownL slot), fun slot => includeR (entry.knownR slot)⟩

/-- Exact equality transfers the earlier proof at each member slot. -/
def reuseGroup [DecidableEq (Ty V S)] {family : Family m} {oldMembers newMembers : List (Function V S)}
    (check : ExactGroupCheck m) (earlier : Group m oldMembers) (group : Group m newMembers)
    (known : ∀ slot, family (earlier.ref slot)) : Option (PLift (∀ slot, family (group.ref slot))) := by
  letI : DecidableEq (Function V S) := decideFunction
  refine if signatures : oldMembers = newMembers then ?_ else none
  subst newMembers
  exact (check group earlier).map fun (same : PLift (group = earlier)) =>
    ⟨fun slot => by rw [same.down]; exact known slot⟩

def GroupEntry.checkAlias [DecidableEq (Ty V S)] {familyL familyR : Family m}
    (entry : GroupEntry familyL familyR) (check : ExactGroupCheck m) {members : List (Function V S)}
    (left right : Group m members) :
    Option (PLift ((∀ slot, familyL (left.ref slot)) ∧ (∀ slot, familyR (right.ref slot)))) := do
  let knownL ← reuseGroup check entry.left left entry.knownL
  let knownR ← reuseGroup check entry.right right entry.knownR
  pure ⟨knownL.down, knownR.down⟩

structure Checked (primitives : Primitives m σ) (ids : GlobalRel) (code : OpcodeCode (Instruction Op))
    (captureCode : CaptureCode m)
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR) where
  familyL : Family m
  familyR : Family m
  keys : DispatchKeys V S code.Key captureCode.Key
  certified : LinkedFamily primitives ids code captureCode familyL familyR keys
  lambdas : List (LambdaEntry familyL familyR)
  groups : List (GroupEntry familyL familyR)
  left : Table familyL localsL
  right : Table familyR localsR

/-- Install both actual linked rows using membership from a checked alias. -/
def Checked.aliasRows {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (earlier : Checked primitives ids code captureCode localsL localsR)
    {fn : Function V S} {left right : m.Val fn.port} (known : earlier.familyL left ∧ earlier.familyR right) :
    Checked primitives ids code captureCode (localsL.snoc (.cons left .nil)) (localsR.snoc (.cons right .nil)) :=
  ⟨earlier.familyL, earlier.familyR, earlier.keys, earlier.certified, earlier.lambdas, earlier.groups,
    earlier.left.snoc (singletonRow known.1), earlier.right.snoc (singletonRow known.2)⟩

/-- Install the actual linked aliases using the existing dispatch family. -/
def Checked.aliasGroupRows {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (earlier : Checked primitives ids code captureCode localsL localsR) {members : List (Function V S)}
    (left right : Group m members) (knownL : ∀ slot, earlier.familyL (left.ref slot))
    (knownR : ∀ slot, earlier.familyR (right.ref slot)) :
    Checked primitives ids code captureCode (localsL.snoc (memberValues members left.ref))
      (localsR.snoc (memberValues members right.ref)) :=
  ⟨earlier.familyL, earlier.familyR, earlier.keys, earlier.certified, earlier.lambdas, earlier.groups,
    earlier.left.snoc (memberRow members left.ref knownL), earlier.right.snoc (memberRow members right.ref knownR)⟩

section LambdaAdmission

variable [DecidableEq (Ty V S)] {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
variable {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
variable {fn : Function V S}

/-- Extend the checked dispatch prefix by a fresh row and install the
actual linked values in the typed locals. -/
def Checked.freshLambda [DecidableEq code.Key] (ordinary : OrdinaryOutputs Op)
    (earlier : Checked primitives ids code captureCode localsL localsR)
    (entryL : Tuple m.Val importsL) (entryR : Tuple m.Val importsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) :
    Option (Checked primitives ids code captureCode
      (localsL.snoc (.cons (linkedLambda left entryL localsL) .nil))
      (localsR.snoc (.cons (linkedLambda right entryR localsR) .nil))) :=
  match earlier.certified.addLambda code ordinary (entryL := entryL) (entryR := entryR)
    (earlier.left.available earlier.certified.ordinaryL) (earlier.right.available earlier.certified.ordinaryR)
    left right with
  | none => none
  | some certified =>
    let calleeL := linkedLambda left entryL localsL
    let calleeR := linkedLambda right entryR localsR
    let familyL : Family m := WithExport earlier.familyL calleeL
    let familyR : Family m := WithExport earlier.familyR calleeR
    let entry : LambdaEntry familyL familyR := ⟨fn, calleeL, calleeR, .exported, .exported⟩
    let tableL := (earlier.left.lift (fun known => WithExport.inherited known)).snoc (singletonRow entry.knownL)
    let tableR := (earlier.right.lift (fun known => WithExport.inherited known)).snoc (singletonRow entry.knownR)
    let groups := earlier.groups.map (GroupEntry.lift WithExport.inherited WithExport.inherited)
    some ⟨familyL, familyR, _, certified.down, entry :: earlier.lambdas.map LambdaEntry.inherit, groups, tableL, tableR⟩

/-- The new values have different keys from every previously admitted λ
on their own sides. Cross-side separation is checked by `freshLambda`. -/
def Checked.DistinctLambdas (earlier : Checked primitives ids code captureCode localsL localsR)
    (entryL : Tuple m.Val importsL) (entryR : Tuple m.Val importsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) : Prop :=
  (lambdaBodyKey code captureCode left entryL localsL).Fresh earlier.keys.left ∧
    (lambdaBodyKey code captureCode right entryR localsR).Fresh earlier.keys.right

instance [DecidableEq code.Key] (earlier : Checked primitives ids code captureCode localsL localsR)
    (entryL : Tuple m.Val importsL) (entryR : Tuple m.Val importsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) :
    Decidable (earlier.DistinctLambdas entryL entryR left right) := by
  letI := captureCode.decideKey
  unfold Checked.DistinctLambdas
  infer_instance

omit [DecidableEq (Ty V S)] in
theorem Checked.notKnown_of_distinct (earlier : Checked primitives ids code captureCode localsL localsR)
    {entryL : Tuple m.Val importsL} {entryR : Tuple m.Val importsR}
    {left : Lambda Op importsL pastL fn} {right : Lambda Op importsR pastR fn}
    (distinct : earlier.DistinctLambdas entryL entryR left right) :
    (¬earlier.familyL (linkedLambda left entryL localsL)) ∧ (¬earlier.familyR (linkedLambda right entryR localsR)) :=
  ⟨fun known => distinct.1 (earlier.certified.keysL known rfl),
    fun known => distinct.2 (earlier.certified.keysR known rfl)⟩

/-- The alias branch carries the first bilateral match. The fresh branch
carries the checked extension and excludes prior membership on either side. -/
inductive LambdaAdmission (check : ExactValueCheck m)
    (earlier : Checked primitives ids code captureCode localsL localsR) (left right : m.Val fn.port) where
  | alias (hit : AliasMatch earlier.lambdas check (fn := fn) left right)
  | fresh (distinct : (¬earlier.familyL left) ∧ (¬earlier.familyR right))
      (extended : Checked primitives ids code captureCode (localsL.snoc (.cons left .nil)) (localsR.snoc (.cons right .nil)))

def LambdaAdmission.toChecked {check : ExactValueCheck m}
    {earlier : Checked primitives ids code captureCode localsL localsR} {left right : m.Val fn.port} :
    LambdaAdmission check earlier (fn := fn) left right →
      Checked primitives ids code captureCode (localsL.snoc (.cons left .nil)) (localsR.snoc (.cons right .nil))
  | .alias hit => earlier.aliasRows (fn := fn) hit.known
  | .fresh _ extended => extended

/-- Prefer a proved bilateral alias. A miss proceeds only with independent
evidence of same-side distinctness, as well as the existing checks for a
fresh row's cross-side separation, capture membership and ordered body. -/
def Checked.autoLambda [DecidableEq code.Key] (ordinary : OrdinaryOutputs Op) (check : ExactValueCheck m)
    (earlier : Checked primitives ids code captureCode localsL localsR)
    (entryL : Tuple m.Val importsL) (entryR : Tuple m.Val importsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) :
    Option (LambdaAdmission check earlier (fn := fn) (linkedLambda left entryL localsL) (linkedLambda right entryR localsR)) :=
  match findAlias earlier.lambdas check (fn := fn) (linkedLambda left entryL localsL) (linkedLambda right entryR localsR) with
  | some hit => some (.alias hit)
  | none =>
    if distinct : earlier.DistinctLambdas entryL entryR left right then
      (earlier.freshLambda ordinary entryL entryR left right).map (.fresh (earlier.notKnown_of_distinct distinct))
    else none

variable [DecidableEq code.Key]
variable (ordinary : OrdinaryOutputs Op) (check : ExactValueCheck m)
variable (earlier : Checked primitives ids code captureCode localsL localsR)
variable (entryL : Tuple m.Val importsL) (entryR : Tuple m.Val importsR)
variable (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn)

theorem Checked.autoLambda_alias
    {hit : AliasMatch earlier.lambdas check (fn := fn) (linkedLambda left entryL localsL) (linkedLambda right entryR localsR)}
    (found : findAlias earlier.lambdas check (fn := fn)
      (linkedLambda left entryL localsL) (linkedLambda right entryR localsR) = some hit) :
    earlier.autoLambda ordinary check entryL entryR left right = some (.alias hit) := by
  simp [autoLambda, found]

theorem Checked.autoLambda_fresh
    (miss : findAlias earlier.lambdas check (fn := fn)
      (linkedLambda left entryL localsL) (linkedLambda right entryR localsR) = none)
    (distinct : earlier.DistinctLambdas entryL entryR left right) :
    earlier.autoLambda ordinary check entryL entryR left right =
      (earlier.freshLambda ordinary entryL entryR left right).map (.fresh (earlier.notKnown_of_distinct distinct)) := by
  simp [autoLambda, miss, distinct]

/-- After an alias miss, equality with any prior admitted value on either
side rules out a fresh extension. This also covers split matches. -/
theorem Checked.autoLambda_rejectKnown
    (miss : findAlias earlier.lambdas check (fn := fn)
      (linkedLambda left entryL localsL) (linkedLambda right entryR localsR) = none)
    (known : earlier.familyL (linkedLambda left entryL localsL) ∨ earlier.familyR (linkedLambda right entryR localsR)) :
    earlier.autoLambda ordinary check entryL entryR left right = none := by
  have collision : ¬earlier.DistinctLambdas entryL entryR left right := fun distinct =>
    known.elim (earlier.notKnown_of_distinct distinct).1 (earlier.notKnown_of_distinct distinct).2
  simp [autoLambda, miss, collision]

end LambdaAdmission

inductive State (primitives : Primitives m σ) (ids : GlobalRel) (code : OpcodeCode (Instruction Op))
    (captureCode : CaptureCode m)
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR) : Bool → Type (max u v w) where
  | unseeded : State primitives ids code captureCode localsL localsR false
  | seeded (checked : Checked primitives ids code captureCode localsL localsR) : State primitives ids code captureCode localsL localsR true

def State.skipL {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR} {ports : Ports (Ty V S)}
    (values : Tuple m.Val ports) :
    {seeded : Bool} → State primitives ids code captureCode localsL localsR seeded → State primitives ids code captureCode (localsL.snoc values) localsR seeded
  | _, .unseeded => .unseeded
  | _, .seeded checked =>
    .seeded ⟨checked.familyL, checked.familyR, checked.keys, checked.certified, checked.lambdas, checked.groups, checked.left.snoc (fun _ => none), checked.right⟩

def State.skipR {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR} {ports : Ports (Ty V S)}
    (values : Tuple m.Val ports) :
    {seeded : Bool} → State primitives ids code captureCode localsL localsR seeded → State primitives ids code captureCode localsL (localsR.snoc values) seeded
  | _, .unseeded => .unseeded
  | _, .seeded checked =>
    .seeded ⟨checked.familyL, checked.familyR, checked.keys, checked.certified, checked.lambdas, checked.groups, checked.left, checked.right.snoc (fun _ => none)⟩

/-- The certificate is indexed by the ordinary executable link outcomes.
A successful certificate consumes the exact exported values at the selected
port, independently of how the paired link relation was obtained. -/
def AdmittedExport (primitives : Primitives m σ) (ids : GlobalRel) {fn : Function V S}
    (port : Port exports fn.port) : Outcome m σ exports → Outcome m σ exports → Prop
  | .linked left _, .linked right _ => ExportAdmission primitives ids (left.get port) (right.get port)
  | _, _ => False

abbrev linkTerm (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (term : ModuleTerm Op imports past sigs exports) (store : σ) : Outcome m σ exports :=
  Executable.linkTable actions unitId inputs past sigs locals term.vertices term.results store

theorem linkTerm_bind (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) {ports : Ports (Ty V S)}
    (definition : VertexTerm Op imports past ports)
    (rest : ModuleTerm Op imports (past ++ [ports]) sigs exports) (store : σ) :
    linkTerm actions unitId inputs locals (.bind definition rest) store =
      match Executable.linkVertex actions unitId inputs locals definition.toGraph store with
      | .linked values middle => linkTerm actions unitId inputs (locals.snoc values) rest middle
      | .undefined failure => .undefined failure := by
  unfold linkTerm
  rw [Executable.linkTable, show (ModuleTerm.bind definition rest).vertices 0 = definition.toGraph from Fin.cases_zero,
    show (fun i : Fin sigs.length => (ModuleTerm.bind definition rest).vertices i.succ) = rest.vertices from
      funext fun i => Fin.cases_succ i]
  simp only [ModuleTerm.results, site, Fin.cases_zero]
  cases Executable.linkVertex actions unitId inputs locals definition.toGraph store <;> rfl

variable [DecidableEq (Ty V S)]

/-- Walk each module in its own link order. Skipped rows still run the
actual linker, including any partial δ initialization. The selected φ/λ
rows use the exact values of the linker's non-effectful binding rules. -/
def walk (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (captureCode : CaptureCode m)
    (exactValue : ExactValueCheck m) (exactGroup : ExactGroupCheck m)
    (actions : Actions m σ)
    (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    {fn : Function V S} (port : Port exports fn.port) :
    {seeded : Bool} → {pastL sigsL pastR sigsR : List (Ports (Ty V S))} →
    {left : ModuleTerm Op importsL pastL sigsL exports} → {right : ModuleTerm Op importsR pastR sigsR exports} →
    (localsL : Locals m.Val pastL) → (localsR : Locals m.Val pastR) → (storeL storeR : σ) →
    Plan Op importsL importsR exports seeded left right →
    State actions.toPrimitives ids keys captureCode localsL localsR seeded →
    Option (PLift (AdmittedExport actions.toPrimitives ids port
      (linkTerm actions unitL inputsL localsL left storeL) (linkTerm actions unitR inputsR localsR right storeR)))
  | _, _, _, _, _, _, _, _, _, _, _, .done (left := outputsL) (right := outputsR), .seeded checked => do
    let selectedL ← exportWire (checked.left.available checked.certified.ordinaryL) outputsL port
    let selectedR ← exportWire (checked.right.available checked.certified.ordinaryR) outputsR port
    pure ⟨checked.certified.forExports selectedL.down selectedR.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR, .skipL (node := node) next, state =>
    match ran : Executable.linkVertex actions unitL inputsL localsL node.toGraph storeL with
    | .undefined _ => none
    | .linked values middle => do
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc values) localsR middle storeR next (state.skipL values)
      pure ⟨by rw [linkTerm_bind, ran]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR, .skipR (node := node) next, state =>
    match ran : Executable.linkVertex actions unitR inputsR localsR node.toGraph storeR with
    | .undefined _ => none
    | .linked values middle => do
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        localsL (localsR.snoc values) storeL middle next (state.skipR values)
      pure ⟨by rw [linkTerm_bind, ran]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .seed (membersL := membersL) (membersR := membersR) (left := left) (right := right) next, .unseeded => do
    let groupL : Group m membersL := ⟨_, left.captures.read inputsL localsL, left.toGraph.definitions⟩
    let groupR : Group m membersR := ⟨_, right.captures.read inputsR localsR, right.toGraph.definitions⟩
    let seed ← LinkedFamily.ofGroups keys actions.toPrimitives ids captureCode ordinary groupL groupR
    let leftTable := (Table.empty groupL.In localsL).snoc (memberRow membersL groupL.ref (fun slot => .member slot))
    let rightTable := (Table.empty groupR.In localsR).snoc (memberRow membersR groupR.ref (fun slot => .member slot))
    let group : GroupEntry groupL.In groupR.In := ⟨membersL, membersR, groupL, groupR, Group.In.member, Group.In.member⟩
    let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
      (localsL.snoc (memberValues membersL groupL.ref)) (localsR.snoc (memberValues membersR groupR.ref))
      storeL storeR next (.seeded ⟨groupL.In, groupR.In, DispatchKeys.seed (groupL.profile keys) (groupR.profile keys), seed.down, [], [group], leftTable, rightTable⟩)
    pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .phi (members := members) (left := left) (right := right) next, .seeded earlier => do
    let outerL ← checkWires (earlier.left.available earlier.certified.ordinaryL) left.captures
    let outerR ← checkWires (earlier.right.available earlier.certified.ordinaryR) right.captures
    let groupL : Group m members := ⟨_, left.captures.read inputsL localsL, left.toGraph.definitions⟩
    let groupR : Group m members := ⟨_, right.captures.read inputsR localsR, right.toGraph.definitions⟩
    let certified ← earlier.certified.addGroup keys ordinary groupL groupR outerL.down outerR.down
    let familyL : Family m := WithGroup earlier.familyL groupL
    let familyR : Family m := WithGroup earlier.familyR groupR
    let tableL := (earlier.left.lift (fun known => WithGroup.inherited known)).snoc
      (memberRow members groupL.ref (fun slot => .member slot) : Row familyL (memberValues members groupL.ref))
    let tableR := (earlier.right.lift (fun known => WithGroup.inherited known)).snoc
      (memberRow members groupR.ref (fun slot => .member slot) : Row familyR (memberValues members groupR.ref))
    let lambdas : List (LambdaEntry familyL familyR) := earlier.lambdas.map fun entry =>
      ⟨entry.fn, entry.left, entry.right, .inherited entry.knownL, .inherited entry.knownR⟩
    let group : GroupEntry familyL familyR := ⟨members, members, groupL, groupR, WithGroup.member, WithGroup.member⟩
    let groups := group :: earlier.groups.map (GroupEntry.lift WithGroup.inherited WithGroup.inherited)
    let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
      (localsL.snoc (memberValues members groupL.ref)) (localsR.snoc (memberValues members groupR.ref))
      storeL storeR next (.seeded ⟨familyL, familyR, _, certified.down, lambdas, groups, tableL, tableR⟩)
    pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .phiAlias (members := members) (left := left) (right := right) prior next, .seeded earlier =>
    match earlier.groups[prior]? with
    | none => none
    | some entry => do
      let groupL : Group m members := ⟨_, left.captures.read inputsL localsL, left.toGraph.definitions⟩
      let groupR : Group m members := ⟨_, right.captures.read inputsR localsR, right.toGraph.definitions⟩
      let known ← entry.checkAlias exactGroup groupL groupR
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc (memberValues members groupL.ref)) (localsR.snoc (memberValues members groupR.ref))
        storeL storeR next (.seeded (earlier.aliasGroupRows groupL groupR known.down.1 known.down.2))
      pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .lambda (left := left) (right := right) next, .seeded earlier =>
    match earlier.freshLambda ordinary inputsL inputsR left.toGraph right.toGraph with
    | none => none
    | some extended => do
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc (.cons (linkedLambda left.toGraph inputsL localsL) .nil))
        (localsR.snoc (.cons (linkedLambda right.toGraph inputsR localsR) .nil)) storeL storeR next (.seeded extended)
      pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .lambdaAuto (left := left) (right := right) next, .seeded earlier =>
    match earlier.autoLambda ordinary exactValue inputsL inputsR left.toGraph right.toGraph with
    | none => none
    | some admitted => do
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc (.cons (linkedLambda left.toGraph inputsL localsL) .nil))
        (localsR.snoc (.cons (linkedLambda right.toGraph inputsR localsR) .nil)) storeL storeR next
        (.seeded admitted.toChecked)
      pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .alias (fn := fn) (left := left) (right := right) prior next, .seeded earlier =>
    match earlier.lambdas[prior]? with
    | none => none
    | some entry => do
      let calleeL := linkedLambda left.toGraph inputsL localsL
      let calleeR := linkedLambda right.toGraph inputsR localsR
      let known ← entry.checkAlias exactValue (fn := fn) calleeL calleeR
      let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc (.cons calleeL .nil)) (localsR.snoc (.cons calleeR .nil)) storeL storeR next
        (.seeded (earlier.aliasRows (fn := fn) known.down))
      pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .aliasFirst (fn := fn) (left := left) (right := right) next, .seeded earlier => do
    let calleeL := linkedLambda left.toGraph inputsL localsL
    let calleeR := linkedLambda right.toGraph inputsR localsR
    let hit ← findAlias earlier.lambdas exactValue (fn := fn) calleeL calleeR
    let checked ← walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
      (localsL.snoc (.cons calleeL .nil)) (localsR.snoc (.cons calleeR .nil)) storeL storeR next
      (.seeded (earlier.aliasRows (fn := fn) hit.known))
    pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩

/-- Check an ordered pair of complete link prefixes, then read the
selected export from the generated membership tables. The plan contains
only binding selections. Each λ step checks separation using actual
capture observations as well as the body profile. An alias row requires
certificates of actual value equality on both sides. `Plan.phiAlias`
checks the actual group on each side. The default group check uses
`exactValue` for outer captures. `Plan.lambdaAuto`
selects between the first proved alias and a checked fresh extension.
Related successful link
outcomes and primitive compatibility remain premises for paired invocation. -/
def admit (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (actions : Actions m σ)
    (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (left : OmegaTerm Op importsL exports sigsL) (right : OmegaTerm Op importsR exports sigsR)
    (plan : Plan Op importsL importsR exports false left.region right.region)
    {fn : Function V S} (port : Port exports fn.port) (storeL storeR : σ)
    (captureCode : CaptureCode m := .controlOnly m)
    (exactValue : ExactValueCheck m := fun _ _ => none)
    (exactGroup : ExactGroupCheck m := ExactGroupCheck.ofCaptures keys exactValue) :
    Option (PLift (AdmittedExport actions.toPrimitives ids port
      (Executable.link actions unitL left.toGraph inputsL storeL)
      (Executable.link actions unitR right.toGraph inputsR storeR))) :=
  walk keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port (pastL := []) (pastR := [])
    (left := left.region) (right := right.region) PUnit.unit PUnit.unit storeL storeR plan .unseeded

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
