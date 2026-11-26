module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Decision.Defs
public import Mathlib.Data.Multiset.Defs

/-! Admission for λ exports and fixed φ member groups. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Continuation.Partial (Primitives)
open NestedTheta.Equality (KindCode OpcodeCode kindCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)}

/-- Ordinary ports do not contain callable values, including inside a global. -/
def ordinarySort : ValueSort V S → Bool
  | .data _ => true
  | .function _ _ => false
  | .global value => ordinarySort value

def ordinaryPort : Ty V S → Bool
  | .value value => ordinarySort value
  | .control _ | .state _ => true

abbrev ordinaryPorts (ports : Ports (Ty V S)) : Bool := ports.all ordinaryPort

/-- A conservative primitive interface. The runtime may read callables,
but each successful primitive output consists entirely of ordinary ports. -/
def OrdinaryOutputs (Op : Dialect.{u, v} (ValueSort V S) S) : Prop :=
  ∀ {input output : Ports (Ty V S)}, Op input output → ordinaryPorts output = true

/-- The exact outer capture tuple and definition table stored by a linked
member. The family includes every fixed slot of this group. -/
structure Group (m : Machine.{u, v, w} Op) (members : List (Function V S)) where
  context : Ports (Ty V S)
  values : Tuple m.Val context
  definitions : MemberTable Op context members

def Group.ref {members : List (Function V S)} (group : Group m members)
    (slot : Fin members.length) : m.Val members[slot].port :=
  .member group.values group.definitions slot

/-- Related members share the ordered group signatures and capture types. -/
abbrev GroupKey (V S : Type u) := List (Function V S) × Ports (Ty V S)

def Group.key {members : List (Function V S)} (group : Group m members) : GroupKey V S :=
  (members, group.context)

/-- Extend a checked family with the actual member values of one group. -/
inductive WithGroup (earlier : Family m) {members : List (Function V S)} (group : Group m members) : Family m where
  | inherited {port : Ty V S} {value : m.Val port} (known : earlier value) : WithGroup earlier group value
  | member (slot : Fin members.length) : WithGroup earlier group (group.ref slot)

inductive Group.In {members : List (Function V S)} (group : Group m members) : Family m where
  | ordinary {port : Ty V S} (value : m.Val port) (plain : ordinaryPort port = true) : Group.In group value
  | member (slot : Fin members.length) : Group.In group (group.ref slot)

/-- A standalone family admits ordinary values and one exact callable.
The capture check is separate from membership in this family. -/
inductive StandaloneIn (root : m.Val (.value (.function args outs))) : Family m where
  | ordinary {port : Ty V S} (value : m.Val port) (plain : ordinaryPort port = true) : StandaloneIn root value
  | exported : StandaloneIn root root

/-- Extend a callable family with an exact exported value. For the checked
capture case the earlier family is the fixed group captured by the λ. -/
inductive WithExport (earlier : Family m) (root : m.Val (.value (.function args outs))) : Family m where
  | inherited {port : Ty V S} {value : m.Val port} (known : earlier value) : WithExport earlier root value
  | exported : WithExport earlier root root

def isStandaloneLambda {port : Ty V S} : m.Val port → Bool
  | .closure _ _ => true
  | _ => false

/-- Admission for the actual export values. All ordinary entry arguments
are admitted. Callable values obtained by following internal wires stay
within their respective families, including across recursive calls. -/
def ExportAdmission (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : m.Val (.value (.function args outs))) : Prop :=
  ∃ familyL familyR, CheckedFamily primitives ids familyL familyR ∧ familyL left ∧ familyR right ∧
    (∀ {ports : Ports (Ty V S)} (values : Tuple m.Val ports), ordinaryPorts ports = true →
      TupleIn familyL values ∧ TupleIn familyR values)

/-- Recover the actual group and a proof that the export belongs to it. -/
structure ExportGroup {port : Ty V S} (value : m.Val port) where
  members : List (Function V S)
  group : Group m members
  known : group.In value

def exportGroup : {port : Ty V S} → (value : m.Val port) → Option (ExportGroup value)
  | _, .member (members := members) values definitions slot =>
    some ⟨members, ⟨_, values, definitions⟩, .member slot⟩
  | _, _ => none

def memberSlot {port : Ty V S} : m.Val port → Option Nat
  | .member _ _ slot => some slot.val
  | _ => none

/-- This capture policy admits a single direct member among ordinary
captures. It records membership in that member's actual linked group. -/
inductive GroupCaptures {members : List (Function V S)} (group : Group m members) :
    {ports : Ports (Ty V S)} → Tuple m.Val ports → Prop where
  | member {port : Ty V S} {ports : Ports (Ty V S)} {value : m.Val port} {rest : Tuple m.Val ports}
      (known : group.In value) (plain : ordinaryPorts ports = true) : GroupCaptures group (.cons value rest)
  | ordinary {port : Ty V S} {ports : Ports (Ty V S)} {value : m.Val port} {rest : Tuple m.Val ports}
      (plain : ordinaryPort port = true) (captures : GroupCaptures group rest) : GroupCaptures group (.cons value rest)

structure CapturedGroup {ports : Ports (Ty V S)} (values : Tuple m.Val ports) where
  members : List (Function V S)
  group : Group m members
  slot : Option Nat
  captures : GroupCaptures group values

/-- Extract the actual captured member and its definition table. Ordinary
captures before or after it are admitted by their port types. -/
def capturedGroup : {ports : Ports (Ty V S)} → (values : Tuple m.Val ports) → Option (CapturedGroup values)
  | _, .nil => none
  | _, .cons (t := port) (ts := ports) value rest =>
    if ordinary : ordinaryPort port = true then
      (capturedGroup rest).map fun found => ⟨found.members, found.group, found.slot, .ordinary ordinary found.captures⟩
    else if plain : ordinaryPorts ports = true then
      (exportGroup value).map fun found => ⟨found.members, found.group, memberSlot value, .member found.known plain⟩
    else none

/-- A numbered vertex contributes its ordered operand and result types
and the code of its kind, including the opcode for primitives and applies. -/
abbrev LabelCode (V S : Type u) (Key : Type v) := Ports (Ty V S) × Ports (Ty V S) × KindCode Key

def labelCode (code : OpcodeCode (Instruction Op)) (label : NestedTheta.NodeLabel (Instruction Op)) :
    LabelCode V S code.Key :=
  (label.ins, label.outs, kindCode code label.kind)

def outerLabels (code : OpcodeCode (Instruction Op)) {sigs : List (Ports (Ty V S))}
    (body : Graph Op args [] sigs outs) : List (LabelCode V S code.Key) :=
  List.ofFn fun i => labelCode code (body.nodes i).label

/-- The multiset of outer vertex labels forgets numbering. The ordered
body checker still verifies execution order. -/
def outerProfile (code : OpcodeCode (Instruction Op)) {sigs : List (Ports (Ty V S))}
    (body : Graph Op args [] sigs outs) : Multiset (LabelCode V S code.Key) :=
  Multiset.ofList (outerLabels code body)

/-- Every fixed member slot contributes the multiset of typed outer labels
of its definition. Slot order is significant, and vertex numbering is forgotten. -/
abbrev GroupProfile (V S : Type u) (Key : Type v) :=
  GroupKey V S × List (Multiset (LabelCode V S Key))

def definitionProfiles (code : OpcodeCode (Instruction Op)) {context : Ports (Ty V S)}
    {members : List (Function V S)} (table : MemberTable Op context members) :
    List (Multiset (LabelCode V S code.Key)) :=
  List.ofFn fun slot => outerProfile code (table slot).body

def Group.profile (code : OpcodeCode (Instruction Op)) {members : List (Function V S)}
    (group : Group m members) : GroupProfile V S code.Key :=
  (group.key, definitionProfiles code group.definitions)

def memberProfile (code : OpcodeCode (Instruction Op)) {port : Ty V S} : m.Val port → Option (GroupProfile V S code.Key)
  | .member (members := members) (context := context) _ table _ =>
    some ((members, context), definitionProfiles code table)
  | _ => none

/-- Observable projections of typed data and state. An omitted projection
leaves that value inconclusive. Equal runtime values always have equal codes. -/
structure CaptureCode (m : Machine.{u, v, w} Op) where
  Key : Type w
  decideKey : DecidableEq Key
  data : {t : V} → m.Data t → Option Key
  state : {t : S} → m.State t → Option Key

def CaptureCode.controlOnly (m : Machine.{u, v, w} Op) : CaptureCode m :=
  ⟨PUnit, inferInstance, fun _ => none, fun _ => none⟩

/-- Related globals have related payloads even when their addresses differ.
Callable values contribute no observation. -/
def CaptureCode.value (code : CaptureCode m) : {port : Ty V S} → m.Val port → Option (Nat ⊕ code.Key)
  | _, .data value => (code.data value).map Sum.inr
  | _, .state value => (code.state value).map Sum.inr
  | _, .control tag => some (.inl tag.val)
  | _, .global _ _ payload => code.value payload
  | _, .closure .. | _, .member .. => none

def CaptureCode.tuple (code : CaptureCode m) : {ports : Ports (Ty V S)} →
    Tuple m.Val ports → List (Option (Nat ⊕ code.Key))
  | _, .nil => []
  | _, .cons head tail => code.value head :: code.tuple tail

/-- An optional certificate of exact equality between actual runtime
values. A missing certificate leaves the comparison inconclusive. -/
abbrev ExactValueCheck (m : Machine.{u, v, w} Op) :=
  {port : Ty V S} → (left right : m.Val port) → Option (PLift (left = right))

namespace ExactValueCheck

def firstOrder (dataEq : ∀ t, DecidableEq (m.Data t)) (stateEq : ∀ t, DecidableEq (m.State t)) :
    ExactValueCheck m
  | _, .data (t := t) left, .data right =>
    letI := dataEq t
    if same : left = right then some ⟨congrArg Colour.data same⟩ else none
  | _, .state (t := t) left, .state right =>
    letI := stateEq t
    if same : left = right then some ⟨congrArg Colour.state same⟩ else none
  | _, .control left, .control right =>
    if same : left = right then some ⟨congrArg Colour.control same⟩ else none
  | _, .global unitL vertexL left, .global unitR vertexR right =>
    if same : unitL = unitR ∧ vertexL = vertexR then do
      let payload ← firstOrder dataEq stateEq left right
      pure ⟨by rw [same.1, same.2, payload.down]⟩
    else none
  | _, _, _ => none

def tuple (check : ExactValueCheck m) : {ports : Ports (Ty V S)} →
    (left right : Tuple m.Val ports) → Option (PLift (left = right))
  | _, .nil, .nil => some ⟨rfl⟩
  | _, .cons left restL, .cons right restR => do
    let head ← check left right
    let tail ← tuple check restL restR
    pure ⟨congrArg₂ Tuple.cons head.down tail.down⟩

/-- Compare λ bodies at their actual numbering and compare the exact
captured values with the supplied checker. Global equality in `firstOrder`
uses the full identity as well as the payload. -/
def lambda [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (captures : ExactValueCheck m) : ExactValueCheck m
  | _, .closure (context := contextL) (sigs := sigsL) valuesL bodyL,
      .closure (context := contextR) (sigs := sigsR) valuesR bodyR => by
    letI : DecidableEq (Ports (Ty V S)) := inferInstance
    letI : DecidableEq (List (Ports (Ty V S))) := inferInstance
    refine if context : contextL = contextR then ?_ else none
    subst contextR
    refine if sigs : sigsL = sigsR then ?_ else none
    subst sigsR
    letI := NestedTheta.Equality.decideGraph keys bodyL bodyR
    exact if body : bodyL = bodyR then
      (tuple captures valuesL valuesR).map fun same =>
        ⟨by rw [body, same.down]⟩
    else none
  | _, _, _ => none

end ExactValueCheck

/-- Optional exact evidence on the actual groups returned by linking. -/
abbrev ExactGroupCheck (m : Machine.{u, v, w} Op) :=
  {members : List (Function V S)} → (left right : Group m members) → Option (PLift (left = right))

namespace ExactGroupCheck

/-- A stored member definition includes its capture origins as well as its
numbered body. Both are compared inside the original scopes. -/
def definition [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {imports : Ports (Ty V S)} {past : List (Ports (Ty V S))} {fn : Function V S}
    (left right : Lambda Op imports past fn) : Option (PLift (left = right)) := by
  obtain ⟨contextL, capturesL, sigsL, bodyL⟩ := left
  obtain ⟨contextR, capturesR, sigsR, bodyR⟩ := right
  letI : DecidableEq (Ports (Ty V S)) := inferInstance
  letI : DecidableEq (List (Ports (Ty V S))) := inferInstance
  refine if context : contextL = contextR then ?_ else none
  subst contextR
  refine if sigs : sigsL = sigsR then ?_ else none
  subst sigsR
  letI := NestedTheta.Equality.decideGraph keys bodyL bodyR
  exact if wiring : capturesL.addresses = capturesR.addresses then
    if body : bodyL = bodyR then
      some ⟨by rw [NestedTheta.Equality.addresses_injective _ _ wiring, body]⟩
    else none
  else none

/-- Exact group comparison with an optional exact-value checker for outer
captures. Every declared slot is checked, including slots absent from exports. -/
def ofCaptures [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (captures : ExactValueCheck m) : ExactGroupCheck m := by
  intro members left right
  obtain ⟨contextL, valuesL, tableL⟩ := left
  obtain ⟨contextR, valuesR, tableR⟩ := right
  letI : DecidableEq (Ports (Ty V S)) := inferInstance
  refine if context : contextL = contextR then ?_ else none
  subst contextR
  exact if slots : ∀ i, (definition keys (tableL i) (tableR i)).isSome = true then
    (ExactValueCheck.tuple captures valuesL valuesR).map fun equal =>
      ⟨by rw [equal.down, funext (fun i => ((definition keys (tableL i) (tableR i)).get (slots i)).down)]⟩
  else none

end ExactGroupCheck

abbrev LambdaSummary (V S : Type u) (Key : Type v) (Capture : Type w) :=
  Ports (Ty V S) × Ports (Ty V S) × Ports (Ty V S) × List (Option (Nat ⊕ Capture)) × Multiset (LabelCode V S Key)

/-- Keep the labels as a list for the executable permutation check. -/
structure LambdaKey (V S : Type u) (Key : Type v) (Capture : Type w) where
  args : Ports (Ty V S)
  results : Ports (Ty V S)
  context : Ports (Ty V S)
  captures : List (Option (Nat ⊕ Capture))
  labels : List (LabelCode V S Key)

def LambdaKey.summary {Key : Type v} {Capture : Type w}
    (key : LambdaKey V S Key Capture) : LambdaSummary V S Key Capture :=
  (key.args, key.results, key.context, key.captures, Multiset.ofList key.labels)

def LambdaKey.Fresh {Key : Type v} {Capture : Type w}
    (key : LambdaKey V S Key Capture) (prior : List (LambdaKey V S Key Capture)) : Prop :=
  key.summary ∉ prior.map LambdaKey.summary

instance [DecidableEq (Ty V S)] {Key : Type v} [DecidableEq Key] {Capture : Type w} [DecidableEq Capture]
    (key : LambdaKey V S Key Capture) (prior : List (LambdaKey V S Key Capture)) : Decidable (key.Fresh prior) :=
  letI : DecidableEq (Ports (Ty V S)) := inferInstance
  letI : DecidableEq (LabelCode V S Key) := inferInstance
  letI : DecidableEq (List (Option (Nat ⊕ Capture))) := inferInstance
  decidable_of_iff (prior.any (fun old => decide
    (key.args = old.args ∧ key.results = old.results ∧ key.context = old.context ∧
      key.captures = old.captures ∧ key.labels.Perm old.labels)) = false) (by
    simp only [List.any_eq_false, decide_eq_true_eq, LambdaKey.Fresh, List.mem_map, not_exists, not_and]
    exact forall_congr' fun old => by
      rw [eq_comm (a := old.summary) (b := key.summary)]
      simp only [LambdaKey.summary, Prod.mk.injEq, Multiset.coe_eq_coe, not_and])

def lambdaKey (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m) {port : Ty V S} :
    m.Val port → Option (LambdaSummary V S code.Key captureCode.Key)
  | .closure (params := params) (results := results) (context := context) captures body =>
    some (params, results, context, captureCode.tuple captures, outerProfile code body)
  | _ => none

def lambdaBodyKey (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    {imports : Ports (Ty V S)} {past : List (Ports (Ty V S))} {fn : Function V S}
    (definition : Lambda Op imports past fn) (entry : Tuple m.Val imports) (locals : Locals m.Val past) :
    LambdaKey V S code.Key captureCode.Key :=
  ⟨fn.args, fn.results, definition.context, captureCode.tuple (definition.captures.read entry locals),
    outerLabels code definition.body⟩

/-- Empty γ rows can be skipped by ordered admission independently on
either side, so retain the actual profiles of each side. -/
structure LambdaKeys (V S : Type u) (Key : Type v) (Capture : Type w) where
  left : List (LambdaKey V S Key Capture)
  right : List (LambdaKey V S Key Capture)

structure DispatchKeys (V S : Type u) (Key : Type v) (Capture : Type w) extends LambdaKeys V S Key Capture where
  groupsL : List (GroupProfile V S Key)
  groupsR : List (GroupProfile V S Key)

def DispatchKeys.seed {Key : Type v} {Capture : Type w} (left right : GroupProfile V S Key) :
    DispatchKeys V S Key Capture :=
  ⟨⟨[], []⟩, [left], [right]⟩

def DispatchKeys.addLambda {Key : Type v} {Capture : Type w} (prior : DispatchKeys V S Key Capture)
    (left right : LambdaKey V S Key Capture) : DispatchKeys V S Key Capture :=
  { prior with left := left :: prior.left, right := right :: prior.right }

def DispatchKeys.addGroup {Key : Type v} {Capture : Type w} (prior : DispatchKeys V S Key Capture)
    (left right : GroupProfile V S Key) : DispatchKeys V S Key Capture :=
  { prior with groupsL := left :: prior.groupsL, groupsR := right :: prior.groupsR }

/-- A checked finite prefix with separate dispatch keys for λs and φ groups. -/
structure LinkedFamily (primitives : Primitives m σ) (ids : GlobalRel)
    (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m) (left right : Family m)
    (keys : DispatchKeys V S code.Key captureCode.Key) : Prop where
  checked : CheckedFamily primitives ids left right
  ordinaryL : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → left value
  ordinaryR : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → right value
  keysL : ∀ {port : Ty V S} {value : m.Val port} {key : LambdaSummary V S code.Key captureCode.Key},
    left value → lambdaKey code captureCode value = some key → key ∈ keys.left.map LambdaKey.summary
  keysR : ∀ {port : Ty V S} {value : m.Val port} {key : LambdaSummary V S code.Key captureCode.Key},
    right value → lambdaKey code captureCode value = some key → key ∈ keys.right.map LambdaKey.summary
  groupsL : ∀ {port : Ty V S} {value : m.Val port} {key : GroupProfile V S code.Key},
    left value → memberProfile code value = some key → key ∈ keys.groupsL
  groupsR : ∀ {port : Ty V S} {value : m.Val port} {key : GroupProfile V S code.Key},
    right value → memberProfile code value = some key → key ∈ keys.groupsR

variable {imports : Ports (Ty V S)} {past : List (Ports (Ty V S))}

/-- Evidence offered for the actual value of a typed origin in a link
prefix. An unchecked origin has no membership certificate. -/
abbrev Available (family : Family m) (entry : Tuple m.Val imports) (locals : Locals m.Val past) :=
  ∀ {port : Ty V S} (origin : Origin imports past port),
    Option (PLift (family ((Wires.read (.cons origin .nil) entry locals).get .head)))

/-- Read the definition's real capture wires and collect the exact
membership evidence from the already checked binding positions. -/
def checkWires {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (available : Available family entry locals) :
    {ports : Ports (Ty V S)} → (wires : Wires imports past ports) →
    Option (PLift (TupleIn family (wires.read entry locals)))
  | _, .nil => some ⟨trivial⟩
  | _, .cons origin rest => do
    let head ← available origin
    let tail ← checkWires available rest
    pure ⟨⟨head.down, tail.down⟩⟩

/-- The exact closure returned by linking a λ binding. -/
abbrev linkedLambda {fn : Function V S} (definition : Lambda Op imports past fn)
    (entry : Tuple m.Val imports) (locals : Locals m.Val past) : m.Val fn.port :=
  (lambdaValue m entry locals definition).get .head

variable [DecidableEq (Ty V S)]

/-- Check all slots using the resolved bodies with actual captures. -/
def checkGroupBodies (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {members : List (Function V S)} (left right : Group m members) : Bool :=
  (List.ofFn (fun slot : Fin members.length =>
    (inferResolved keys (resolve m (left.ref slot)) (resolve m (right.ref slot))).isSome)).all id

def checkGroups (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {members : List (Function V S)} (left right : Group m members) : Bool :=
  ordinaryPorts left.context && ordinaryPorts right.context && checkGroupBodies keys left right

def decideFunction (a b : Function V S) : Decidable (a = b) :=
  decidable_of_iff (a.args = b.args ∧ a.results = b.results) (by cases a; cases b; simp)

/-- Compare the exact member signatures in slot order before using the
common table-indexed checker. -/
def checkGroupPair (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {membersL membersR : List (Function V S)} (left : Group m membersL) (right : Group m membersR) : Bool :=
  letI : DecidableEq (Function V S) := decideFunction
  if same : membersL = membersR then checkGroups keys left (same.symm ▸ right) else false

def checkCapturedGroups (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    {portsL portsR : Ports (Ty V S)} (left : Tuple m.Val portsL) (right : Tuple m.Val portsR) : Bool :=
  match capturedGroup left, capturedGroup right with
  | some left, some right => left.slot == right.slot && checkGroupPair keys left.group right.group
  | _, _ => false

/-- Select the finite families directly from two actual exported values.
Paired λ closures admit ordinary captures or one matched φ member each.
The φ groups must have ordinary outer captures. Paired invocation also
uses linker provenance and compatible primitives. -/
def checkExport (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (left right : m.Val (.value (.function args outs))) : Bool :=
  if isStandaloneLambda left && isStandaloneLambda right then
    let bodyL := resolve m left
    let bodyR := resolve m right
    (ordinaryPorts bodyL.context && ordinaryPorts bodyR.context ||
      checkCapturedGroups keys bodyL.values bodyR.values) && (inferResolved keys bodyL bodyR).isSome
  else
    match exportGroup left, exportGroup right with
    | some left, some right => checkGroupPair keys left.group right.group
    | _, _ => false

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
