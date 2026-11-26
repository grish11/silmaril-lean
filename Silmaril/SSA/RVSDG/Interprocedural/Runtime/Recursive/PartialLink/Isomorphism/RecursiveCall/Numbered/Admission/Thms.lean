module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Groups

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Continuation.Partial (Config Primitives)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {primitives : Primitives m σ}

theorem checkExport_sound [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]
    (ordinary : OrdinaryOutputs Op) {left right : m.Val (.value (.function args outs))}
    (accepted : checkExport keys left right = true) : ExportAdmission primitives ids left right :=
  AdmissionProofs.checkExport_sound ordinary accepted

/-- Produce closed-family evidence from the checked linked origins and the
dialect's output restriction. Primitive compatibility is a separate premise
when using the resulting family to compare runs. -/
@[expose] def admitExport [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (primitives : Primitives m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op)
    (left right : m.Val (.value (.function args outs))) : Option (PLift (ExportAdmission primitives ids left right)) :=
  if accepted : checkExport keys left right = true then some ⟨checkExport_sound ordinary accepted⟩ else none

theorem LinkedFamily.ofGroups_sound [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] (captureCode : CaptureCode m) (ordinary : OrdinaryOutputs Op) {membersL membersR : List (Function V S)}
    (left : Group m membersL) (right : Group m membersR) (accepted : checkGroupPair keys left right = true) :
    LinkedFamily primitives ids keys captureCode left.In right.In (DispatchKeys.seed (left.profile keys) (right.profile keys)) :=
  AdmissionProofs.linked_groups captureCode ordinary left right accepted

/-- Seed ordered admission from the actual tables of two earlier linked
φ groups. Their fixed recursive slots stay within those tables. -/
@[expose] def LinkedFamily.ofGroups [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (primitives : Primitives m σ) (ids : GlobalRel) (captureCode : CaptureCode m) (ordinary : OrdinaryOutputs Op)
    {membersL membersR : List (Function V S)} (left : Group m membersL) (right : Group m membersR) :
    Option (PLift (LinkedFamily primitives ids keys captureCode left.In right.In (DispatchKeys.seed (left.profile keys) (right.profile keys)))) :=
  if accepted : checkGroupPair keys left right = true then some ⟨ofGroups_sound captureCode ordinary left right accepted⟩ else none

theorem LinkedFamily.extendGroup [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {prior : DispatchKeys V S keys.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids keys captureCode familyL familyR prior)
    {members : List (Function V S)} (left right : Group m members)
    (fresh : left.profile keys ∉ prior.groupsR ∧ right.profile keys ∉ prior.groupsL)
    (outerL : TupleIn familyL left.values) (outerR : TupleIn familyR right.values)
    (bodies : checkGroupBodies keys left right = true) :
    LinkedFamily primitives ids keys captureCode (WithGroup familyL left) (WithGroup familyR right)
      (prior.addGroup (left.profile keys) (right.profile keys)) :=
  AdmissionProofs.linked_group_extension ordinary earlier left right fresh outerL outerR bodies

/-- Admit a new group with checked earlier captures and one matched body per
slot. Profiles distinguish earlier opposite-side groups by interface or by
a difference in the outer labels of a corresponding member definition. -/
@[expose] def LinkedFamily.addGroup [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op))
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {prior : DispatchKeys V S keys.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids keys captureCode familyL familyR prior)
    {members : List (Function V S)} (left right : Group m members)
    (outerL : TupleIn familyL left.values) (outerR : TupleIn familyR right.values) :
    Option (PLift (LinkedFamily primitives ids keys captureCode (WithGroup familyL left) (WithGroup familyR right)
      (prior.addGroup (left.profile keys) (right.profile keys)))) :=
  letI : DecidableEq (Function V S) := decideFunction
  letI : DecidableEq (GroupKey V S) := inferInstance
  letI : DecidableEq (LabelCode V S keys.Key) := inferInstance
  letI : DecidableEq (List (Multiset (LabelCode V S keys.Key))) := inferInstance
  letI : DecidableEq (GroupProfile V S keys.Key) := inferInstance
  if fresh : left.profile keys ∉ prior.groupsR ∧ right.profile keys ∉ prior.groupsL then
    if bodies : checkGroupBodies keys left right = true then
      some ⟨earlier.extendGroup ordinary left right fresh outerL outerR bodies⟩
    else none
  else none

/-- A typed graph renumbering preserves the multiset of its outer labels. -/
theorem outerProfile_eq (code : OpcodeCode (Instruction Op))
    {argsL argsR outsL outsR : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right) :
    outerProfile code left = outerProfile code right :=
  AdmissionProofs.outer_profile code iso

/-- Related members agree on the profile of the entire ordered definition table. -/
theorem memberProfile_eq (code : OpcodeCode (Instruction Op)) {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : memberProfile code left = memberProfile code right :=
  AdmissionProofs.related_memberProfile code related

/-- Distinct capture observations rule out a related tuple for any global
address correspondence. For equal observations the body check still applies. -/
theorem CaptureCode.tuple_eq (code : CaptureCode m) {portsL portsR : Ports (Ty V S)}
    {left : Tuple m.Val portsL} {right : Tuple m.Val portsR}
    (related : TupleRelated m ids left right) : code.tuple left = code.tuple right :=
  AdmissionProofs.capture_tuple_eq code related

theorem lambdaKey_eq (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : lambdaKey code captureCode left = lambdaKey code captureCode right :=
  AdmissionProofs.related_key code captureCode related

theorem LinkedFamily.extend (ordinary : OrdinaryOutputs Op)
    {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {familyL familyR : Family m} {prior : DispatchKeys V S code.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids code captureCode familyL familyR prior)
    {left right : m.Val (.value (.function args outs))}
    {newL newR : LambdaKey V S code.Key captureCode.Key} (fresh : newL.Fresh prior.right ∧ newR.Fresh prior.left)
    (keyL : lambdaKey code captureCode left = some newL.summary) (keyR : lambdaKey code captureCode right = some newR.summary)
    (capturesL : TupleIn familyL (resolve m left).values) (capturesR : TupleIn familyR (resolve m right).values)
    (body : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    LinkedFamily primitives ids code captureCode (WithExport familyL left) (WithExport familyR right) (prior.addLambda newL newR) :=
  AdmissionProofs.linked_extension ordinary earlier fresh keyL keyR capturesL capturesR body

theorem Resolved.context_eq {fn : Function V S} {left right : Closure Op m.Val fn}
    (checked : Resolved m fn left right) : left.context = right.context := by
  cases checked
  rfl

/-- Extend an already checked prefix by one pair of λ definitions. Capture
evidence comes from their typed wires into the actual prefix. Rule out
mixed dispatch in both directions by comparing the signature, actual
capture observations and outer label multiset. Matching observations
fall back to the body profile. Exact duplicates still collide. -/
@[expose] def LinkedFamily.addLambda [DecidableEq (Ty V S)]
    (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] {captureCode : CaptureCode m}
    (ordinary : OrdinaryOutputs Op) {familyL familyR : Family m} {prior : DispatchKeys V S keys.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids keys captureCode familyL familyR prior)
    {importsL importsR : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))} {fn : Function V S}
    {entryL : Tuple m.Val importsL} {entryR : Tuple m.Val importsR}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (availableL : Available familyL entryL localsL) (availableR : Available familyR entryR localsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn) :
    Option (PLift (LinkedFamily primitives ids keys captureCode (WithExport familyL (linkedLambda left entryL localsL))
      (WithExport familyR (linkedLambda right entryR localsR))
      (prior.addLambda (lambdaBodyKey keys captureCode left entryL localsL)
        (lambdaBodyKey keys captureCode right entryR localsR)))) :=
  letI := captureCode.decideKey
  if fresh : (lambdaBodyKey keys captureCode left entryL localsL).Fresh prior.right ∧
      (lambdaBodyKey keys captureCode right entryR localsR).Fresh prior.left then do
    let capturesL ← checkWires availableL left.captures
    let capturesR ← checkWires availableR right.captures
    let body ← inferResolved keys (resolve m (linkedLambda left entryL localsL))
      (resolve m (linkedLambda right entryR localsR))
    pure ⟨earlier.extend ordinary fresh rfl rfl capturesL.down capturesR.down body.down⟩
  else none

theorem LinkedFamily.addLambda_accepts [DecidableEq (Ty V S)]
    (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] {captureCode : CaptureCode m}
    (ordinary : OrdinaryOutputs Op) {familyL familyR : Family m} {prior : DispatchKeys V S keys.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids keys captureCode familyL familyR prior)
    {importsL importsR : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))} {fn : Function V S}
    {entryL : Tuple m.Val importsL} {entryR : Tuple m.Val importsR}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (availableL : Available familyL entryL localsL) (availableR : Available familyR entryR localsR)
    (left : Lambda Op importsL pastL fn) (right : Lambda Op importsR pastR fn)
    (fresh : (lambdaBodyKey keys captureCode left entryL localsL).Fresh prior.right ∧
      (lambdaBodyKey keys captureCode right entryR localsR).Fresh prior.left)
    (capturesL : (checkWires availableL left.captures).isSome = true)
    (capturesR : (checkWires availableR right.captures).isSome = true)
    (body : (inferResolved keys (resolve m (linkedLambda left entryL localsL))
      (resolve m (linkedLambda right entryR localsR))).isSome = true) :
    (earlier.addLambda keys ordinary availableL availableR left right).isSome = true := by
  obtain ⟨_, capL⟩ := Option.isSome_iff_exists.mp capturesL
  obtain ⟨_, capR⟩ := Option.isSome_iff_exists.mp capturesR
  obtain ⟨_, inferred⟩ := Option.isSome_iff_exists.mp body
  simp [addLambda, fresh, capL, capR, inferred]

theorem LinkedFamily.forExports {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {familyL familyR : Family m} {prior : DispatchKeys V S code.Key captureCode.Key}
    (family : LinkedFamily primitives ids code captureCode familyL familyR prior)
    {left right : m.Val (.value (.function args outs))}
    (knownL : familyL left) (knownR : familyR right) : ExportAdmission primitives ids left right :=
  AdmissionProofs.linked_exports family knownL knownR

/-- Use the selected values from the partial linker's related success
outcomes. The roots retain the exact arguments and the common post-link store. -/
theorem ExportAdmission.atExport {exports : Ports (Ty V S)} {valuesL valuesR : Tuple m.Val exports}
    (port : Port exports (.value (.function args outs))) {store : σ} {rename : Nat → Nat}
    (linked : OutcomesRelated m ids σ rename exports (.linked valuesL store) (.linked valuesR store))
    (checked : ExportAdmission primitives ids (valuesL.get port) (valuesR.get port))
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR)
    (ordinary : ordinaryPorts args = true) :
    ∃ familyL familyR, ClosedFamily primitives ids familyL familyR ∧
      Admitted m ids familyL familyR
        (⟨Continuation.start (.call (valuesL.get port) inputL), store⟩ : Config m σ outs)
        ⟨Continuation.start (.call (valuesR.get port) inputR), store⟩ := by
  obtain ⟨left, right, family, calleeL, calleeR, plain⟩ := checked
  cases linked with | linked values =>
    exact ⟨left, right, family.toClosed, .call (values.get port) inputs calleeL calleeR
      (plain inputL ordinary).1 (plain inputR ordinary).2 store⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
