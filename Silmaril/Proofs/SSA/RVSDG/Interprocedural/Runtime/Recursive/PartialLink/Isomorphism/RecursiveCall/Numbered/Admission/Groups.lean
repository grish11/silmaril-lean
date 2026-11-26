module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Thms
import Mathlib.Data.List.FinRange

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.AdmissionProofs

open Continuation.Partial (Primitives)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {members : List (Function V S)} {primitives : Primitives m σ} {ids : GlobalRel}

private abbrev HasOrdinary (family : Family m) : Prop :=
  ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → family value

private theorem ordinary_tuple {family : Family m} (admits : HasOrdinary family)
    {ports : Ports (Ty V S)} (tuple : Tuple m.Val ports) (ordinary : ordinaryPorts ports = true) :
    TupleIn family tuple := by
  induction tuple with
  | nil => trivial
  | cons value tail ih =>
    have both := Bool.and_eq_true_iff.mp ordinary
    exact ⟨admits value both.1, ih both.2⟩

private theorem closed_with_captures {family : Family m}
    (ordinary : OrdinaryOutputs Op) (admits : HasOrdinary family)
    (captures : ∀ {args outs : Ports (Ty V S)} {callee : m.Val (.value (.function args outs))},
      family callee → TupleIn family (resolve m callee).values) : Closed primitives family where
  captures := captures
  primitive := by
    intro _ _ opcode _ _ _ _ output _
    exact ordinary_tuple admits output (ordinary opcode)

private theorem member_values (family : Family m) (members : List (Function V S))
    (refs : (slot : Fin members.length) → m.Val members[slot].port)
    (known : ∀ slot, family (refs slot)) : TupleIn family (memberValues members refs) := by
  induction members with
  | nil => trivial
  | cons _ _ ih => exact ⟨known 0, ih _ (fun _ => known _)⟩

private theorem member_prefix (family : Family m) (members : List (Function V S)) (n : Nat)
    (refs : (slot : Fin members.length) → m.Val members[slot].port)
    (known : ∀ slot, family (refs slot)) : LocalsIn family (memberPrefix members n refs) := by
  induction members generalizing n with
  | nil => cases n <;> trivial
  | cons _ _ ih =>
    cases n with
    | zero => trivial
    | succ n => exact ⟨⟨known 0, trivial⟩, ih n _ (fun _ => known _)⟩

private theorem member_captures {family : Family m} (group : Group m members)
    (outer : TupleIn family group.values) (known : ∀ i, family (group.ref i)) (slot : Fin members.length) :
    TupleIn family (resolve m (group.ref slot)).values :=
  TupleIn.read (group.definitions slot).captures
    (TupleIn.prepend (member_values family members group.ref known) outer)
    (member_prefix family members slot.val group.ref known)

private theorem closed (ordinary : OrdinaryOutputs Op) (group : Group m members)
    (outer : ordinaryPorts group.context = true) : Closed primitives group.In := by
  apply closed_with_captures ordinary Group.In.ordinary
  intro args outs callee admitted
  cases admitted with
  | ordinary _ plain => cases plain
  | member slot => exact member_captures group (ordinary_tuple Group.In.ordinary group.values outer) .member slot

private theorem member_origin {group : Group m members} {port : Ty V S} {value : m.Val port}
    (known : group.In value) (callable : ordinaryPort port = false) :
    ∃ slot : Fin members.length,
      (⟨port, value⟩ : (t : Ty V S) × m.Val t) = ⟨members[slot].port, group.ref slot⟩ := by
  cases known with
  | ordinary _ plain => rw [callable] at plain; cases plain
  | member slot => exact ⟨slot, rfl⟩

private theorem related_slot {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : memberSlot left = memberSlot right := by
  cases related <;> rfl

private theorem closed_standalone (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    (root : m.Val (.value (.function args outs))) (plain : ordinaryPorts (resolve m root).context = true) :
    Closed primitives (StandaloneIn root) := by
  apply closed_with_captures ordinary StandaloneIn.ordinary
  intro _ _ _ known
  cases known with
  | ordinary _ plain => cases plain
  | exported => exact ordinary_tuple StandaloneIn.ordinary (resolve m root).values plain

private theorem checked_standalone (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    (left right : m.Val (.value (.function args outs)))
    (plainL : ordinaryPorts (resolve m left).context = true)
    (plainR : ordinaryPorts (resolve m right).context = true)
    (checked : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    CheckedFamily primitives ids (StandaloneIn left) (StandaloneIn right) := by
  refine ⟨closed_standalone ordinary left plainL, closed_standalone ordinary right plainR, ?_⟩
  intro _ _ _ _ knownL knownR _
  cases knownL with
  | ordinary _ plain => cases plain
  | exported =>
    cases knownR with
    | ordinary _ plain => cases plain
    | exported => exact checked

private theorem captured_in {group : Group m members}
    {ports : Ports (Ty V S)} {values : Tuple m.Val ports}
    (captures : GroupCaptures group values) : TupleIn group.In values := by
  induction captures with
  | member known plain => exact ⟨known, ordinary_tuple Group.In.ordinary _ plain⟩
  | ordinary plain _ ih => exact ⟨.ordinary _ plain, ih⟩

private theorem tuple_in_mono {earlier later : Family m}
    (includeValue : ∀ {port : Ty V S} {value : m.Val port}, earlier value → later value)
    {ports : Ports (Ty V S)} {values : Tuple m.Val ports} (known : TupleIn earlier values) : TupleIn later values := by
  induction values with
  | nil => trivial
  | cons _ _ ih => exact ⟨includeValue known.1, ih known.2⟩

private theorem closed_export (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    (root : m.Val (.value (.function args outs))) {earlier : Family m}
    (admits : HasOrdinary earlier) (closed : Closed primitives earlier)
    (rootCaptures : TupleIn earlier (resolve m root).values) : Closed primitives (WithExport earlier root) := by
  apply closed_with_captures ordinary (fun value plain => .inherited (admits value plain))
  intro _ _ _ known
  cases known with
  | inherited known => exact tuple_in_mono WithExport.inherited (closed.captures known)
  | exported => exact tuple_in_mono WithExport.inherited rootCaptures

private theorem member_is_not_lambda {args outs : Ports (Ty V S)}
    {callee : m.Val (.value (.function args outs))} {group : Group m members} (known : group.In callee) :
    isStandaloneLambda callee = false := by
  cases known with
  | ordinary _ plain => cases plain
  | member => rfl

private theorem related_lambda {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : isStandaloneLambda left = isStandaloneLambda right := by
  cases related <;> rfl

private theorem checked_export (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    {left right : m.Val (.value (.function args outs))} {membersL membersR : List (Function V S)}
    {groupL : Group m membersL} {groupR : Group m membersR}
    (earlier : CheckedFamily primitives ids groupL.In groupR.In)
    (shapeL : isStandaloneLambda left = true) (shapeR : isStandaloneLambda right = true)
    (capturedL : GroupCaptures groupL (resolve m left).values)
    (capturedR : GroupCaptures groupR (resolve m right).values)
    (body : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    CheckedFamily primitives ids (WithExport groupL.In left) (WithExport groupR.In right) where
  closedL := closed_export ordinary left Group.In.ordinary earlier.closedL (captured_in capturedL)
  closedR := closed_export ordinary right Group.In.ordinary earlier.closedR (captured_in capturedR)
  graphs := by
    intro _ _ _ _ knownL knownR related
    have paired := related_lambda related
    cases knownL with
    | inherited fromL =>
      cases knownR with
      | inherited fromR => exact earlier.graphs fromL fromR related
      | exported => rw [member_is_not_lambda fromL, shapeR] at paired; cases paired
    | exported =>
      cases knownR with
      | inherited fromR => rw [shapeL, member_is_not_lambda fromR] at paired; cases paired
      | exported => exact body

private theorem group_has_no_key (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    {group : Group m members} {port : Ty V S} {value : m.Val port}
    (known : group.In value) : lambdaKey code captureCode value = none := by
  cases known with
  | ordinary _ plain => cases value <;> first | rfl | cases plain
  | member => rfl

private theorem ofFn_equiv {α : Type*} {n k : Nat} (vertices : Fin n ≃ Fin k) (labels : Fin k → α) :
    (List.ofFn (labels ∘ vertices)).Perm (List.ofFn labels) := by
  have size : n = k := Fin.equiv_iff_eq.mp ⟨vertices⟩
  subst k
  exact Equiv.Perm.ofFn_comp_perm vertices labels

theorem outer_profile (code : OpcodeCode (Instruction Op))
    {argsL argsR outsL outsR : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right) :
    outerProfile code left = outerProfile code right := by
  cases iso with
  | intro _ _ vertices labels _ _ _ =>
    apply Multiset.coe_eq_coe.mpr
    have same : (fun i => labelCode code (left.nodes i).label) =
        (fun i => labelCode code (right.nodes (vertices i)).label) :=
      funext fun i => congrArg (labelCode code) (labels i)
    rw [outerLabels, outerLabels, same]
    exact ofFn_equiv vertices (fun i => labelCode code (right.nodes i).label)

private theorem group_profile_of_known (code : OpcodeCode (Instruction Op)) {group : Group m members}
    {port : Ty V S} {value : m.Val port} {profile : GroupProfile V S code.Key}
    (known : group.In value) (found : memberProfile code value = some profile) : profile = group.profile code := by
  cases known with
  | ordinary _ plain =>
    cases value with
    | member => cases plain
    | _ => cases found
  | member => exact (Option.some.inj found).symm

private theorem memberProfile_of_callable (code : OpcodeCode (Instruction Op))
    {group : Group m members} {args outs : Ports (Ty V S)}
    {value : m.Val (.value (.function args outs))} (known : group.In value) :
    memberProfile code value = some (group.profile code) := by
  cases known with
  | ordinary _ plain => cases plain
  | member => rfl

theorem related_memberProfile (code : OpcodeCode (Instruction Op))
    {port : Ty V S} {left right : m.Val port} (related : ValueRelated m ids left right) :
    memberProfile code left = memberProfile code right := by
  cases related with
  | member _ definitions _ =>
    simp only [memberProfile, Option.some.injEq, Prod.mk.injEq, true_and, definitionProfiles]
    exact congrArg List.ofFn (funext fun slot => outer_profile code (definitions slot).2)
  | _ => rfl

private theorem lambda_has_no_memberProfile {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {port : Ty V S} {value : m.Val port} {key : LambdaSummary V S code.Key captureCode.Key}
    (found : lambdaKey code captureCode value = some key) : memberProfile code value = none := by
  cases value <;> first | rfl | cases found

variable [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]

private theorem checked_member_bodies (left right : Group m members)
    (scanned : checkGroupBodies keys left right = true)
    {args outs : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function args outs))}
    (knownL : left.In calleeL) (knownR : right.In calleeR) (related : ValueRelated m ids calleeL calleeR) :
    Resolved m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR) := by
  have bodies (slot : Fin members.length) :
      (inferResolved keys (resolve m (left.ref slot)) (resolve m (right.ref slot))).isSome = true :=
    List.all_eq_true.mp scanned _ (List.mem_ofFn.mpr ⟨slot, rfl⟩)
  cases knownL with
  | ordinary _ plain => cases plain
  | member slotL =>
    obtain ⟨slotR, origin⟩ := member_origin knownR rfl
    have found := congrArg (fun pair : (t : Ty V S) × m.Val t => memberSlot pair.2) origin
    have same : slotL = slotR := Fin.ext (Option.some.inj ((related_slot related).trans found))
    subst slotR
    have exactRef : calleeR = right.ref slotL := eq_of_heq (Sigma.mk.inj_iff.mp origin).2
    subst calleeR
    exact inferResolved_sound (bodies slotL)

private theorem checked_groups (ordinary : OrdinaryOutputs Op) (left right : Group m members)
    (accepted : checkGroups keys left right = true) : CheckedFamily primitives ids left.In right.In := by
  obtain ⟨plain, scanned⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨plainL, plainR⟩ := Bool.and_eq_true_iff.mp plain
  exact ⟨closed ordinary left plainL, closed ordinary right plainR, checked_member_bodies left right scanned⟩

private theorem checked_group_pair (ordinary : OrdinaryOutputs Op)
    {membersL membersR : List (Function V S)} (left : Group m membersL) (right : Group m membersR)
    (accepted : checkGroupPair keys left right = true) : CheckedFamily primitives ids left.In right.In := by
  unfold checkGroupPair at accepted
  split at accepted
  next same =>
    subst membersR
    exact checked_groups ordinary left right accepted
  next => cases accepted

private theorem checked_captures (ordinary : OrdinaryOutputs Op)
    {args outs : Ports (Ty V S)} {left right : m.Val (.value (.function args outs))}
    (shapeL : isStandaloneLambda left = true) (shapeR : isStandaloneLambda right = true)
    (accepted : checkCapturedGroups keys (resolve m left).values (resolve m right).values = true)
    (body : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    ExportAdmission primitives ids left right := by
  unfold checkCapturedGroups at accepted
  split at accepted
  next foundL foundR _ _ =>
    have earlier := checked_group_pair (primitives := primitives) (ids := ids)
      ordinary foundL.group foundR.group (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨WithExport foundL.group.In left, WithExport foundR.group.In right,
      checked_export ordinary earlier shapeL shapeR foundL.captures foundR.captures body, .exported, .exported,
      fun tuple plain => ⟨ordinary_tuple (fun v h => .inherited (.ordinary v h)) tuple plain,
        ordinary_tuple (fun v h => .inherited (.ordinary v h)) tuple plain⟩⟩
  next => cases accepted

theorem checkExport_sound (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    {left right : m.Val (.value (.function args outs))}
    (accepted : checkExport keys left right = true) : ExportAdmission primitives ids left right := by
  unfold checkExport at accepted
  split at accepted
  next lambdaPair =>
    have ⟨shapeL, shapeR⟩ := Bool.and_eq_true_iff.mp lambdaPair
    obtain ⟨captures, scanned⟩ := Bool.and_eq_true_iff.mp accepted
    have body := inferResolved_sound scanned
    rcases Bool.or_eq_true_iff.mp captures with plain | captured
    · obtain ⟨plainL, plainR⟩ := Bool.and_eq_true_iff.mp plain
      exact ⟨StandaloneIn left, StandaloneIn right,
        checked_standalone ordinary left right plainL plainR body, .exported, .exported,
        fun tuple plain => ⟨ordinary_tuple StandaloneIn.ordinary tuple plain,
          ordinary_tuple StandaloneIn.ordinary tuple plain⟩⟩
    · exact checked_captures ordinary shapeL shapeR captured body
  next =>
    split at accepted
    next l r _ _ =>
      exact ⟨l.group.In, r.group.In, checked_group_pair ordinary l.group r.group accepted, l.known, r.known,
        fun tuple plain => ⟨ordinary_tuple Group.In.ordinary tuple plain,
          ordinary_tuple Group.In.ordinary tuple plain⟩⟩
    next => cases accepted

theorem linked_groups (captureCode : CaptureCode m) (ordinary : OrdinaryOutputs Op) {membersL membersR : List (Function V S)}
    (left : Group m membersL) (right : Group m membersR)
    (accepted : checkGroupPair keys left right = true) : LinkedFamily primitives ids keys captureCode left.In right.In (DispatchKeys.seed (left.profile keys) (right.profile keys)) where
  checked := checked_group_pair ordinary left right accepted
  ordinaryL := Group.In.ordinary
  ordinaryR := Group.In.ordinary
  keysL known key := by rw [group_has_no_key keys captureCode known] at key; cases key
  keysR known key := by rw [group_has_no_key keys captureCode known] at key; cases key

  groupsL known found := by rw [group_profile_of_known keys known found]; exact List.mem_cons_self
  groupsR known found := by rw [group_profile_of_known keys known found]; exact List.mem_cons_self

omit [DecidableEq (Ty V S)] in
private theorem closed_with_group (ordinary : OrdinaryOutputs Op) {family : Family m} (group : Group m members)
    (admits : HasOrdinary family) (closed : Closed primitives family) (outer : TupleIn family group.values) :
    Closed primitives (WithGroup family group) := by
  apply closed_with_captures ordinary (fun value plain => .inherited (admits value plain))
  intro _ _ _ known
  cases known with
  | inherited fromEarlier => exact tuple_in_mono WithGroup.inherited (closed.captures fromEarlier)
  | member slot =>
    exact member_captures group (tuple_in_mono WithGroup.inherited outer) WithGroup.member slot

theorem linked_group_extension (ordinary : OrdinaryOutputs Op) {captureCode : CaptureCode m}
    {familyL familyR : Family m} {prior : DispatchKeys V S keys.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids keys captureCode familyL familyR prior) (left right : Group m members)
    (fresh : left.profile keys ∉ prior.groupsR ∧ right.profile keys ∉ prior.groupsL)
    (outerL : TupleIn familyL left.values) (outerR : TupleIn familyR right.values)
    (bodies : checkGroupBodies keys left right = true) :
    LinkedFamily primitives ids keys captureCode (WithGroup familyL left) (WithGroup familyR right)
      (prior.addGroup (left.profile keys) (right.profile keys)) where
  checked :=
    { closedL := closed_with_group ordinary left earlier.ordinaryL earlier.checked.closedL outerL
      closedR := closed_with_group ordinary right earlier.ordinaryR earlier.checked.closedR outerR
      graphs := by
        intro _ _ calleeL calleeR knownL knownR related
        have leftCases : familyL calleeL ∨ left.In calleeL := by
          cases knownL with
          | inherited known => exact .inl known
          | member slot => exact .inr (.member slot)
        have rightCases : familyR calleeR ∨ right.In calleeR := by
          cases knownR with
          | inherited known => exact .inl known
          | member slot => exact .inr (.member slot)
        have same := related_memberProfile keys related
        rcases leftCases with oldL | newL <;> rcases rightCases with oldR | newR
        · exact earlier.checked.graphs oldL oldR related
        · exact (fresh.2 (earlier.groupsL oldL (same.trans (memberProfile_of_callable keys newR)))).elim
        · exact (fresh.1 (earlier.groupsR oldR (same.symm.trans (memberProfile_of_callable keys newL)))).elim
        · exact checked_member_bodies left right bodies newL newR related }
  ordinaryL value plain := .inherited (earlier.ordinaryL value plain)
  ordinaryR value plain := .inherited (earlier.ordinaryR value plain)
  keysL known found := by
    cases known with
    | inherited old => exact earlier.keysL old found
    | member => cases found
  keysR known found := by
    cases known with
    | inherited old => exact earlier.keysR old found
    | member => cases found
  groupsL known found := by
    cases known with
    | inherited old => exact List.mem_cons_of_mem _ (earlier.groupsL old found)
    | member => cases found; exact List.mem_cons_self
  groupsR known found := by
    cases known with
    | inherited old => exact List.mem_cons_of_mem _ (earlier.groupsR old found)
    | member => cases found; exact List.mem_cons_self

omit [DecidableEq (Ty V S)] in
private theorem capture_value_eq (code : CaptureCode m) :
    ∀ {port : Ty V S} {left right : m.Val port}, ValueRelated m ids left right → code.value left = code.value right
  | _, _, _, .global _ payload => by
    simp only [CaptureCode.value]
    exact capture_value_eq code payload
  | _, _, _, .data _ | _, _, _, .state _ | _, _, _, .control _
  | _, _, _, .closure _ _ | _, _, _, .member _ _ _ => rfl
termination_by structural _ _ _ related => related

omit [DecidableEq (Ty V S)] in
theorem capture_tuple_eq (code : CaptureCode m) :
    ∀ {portsL portsR : Ports (Ty V S)} {left : Tuple m.Val portsL} {right : Tuple m.Val portsR},
      TupleRelated m ids left right → code.tuple left = code.tuple right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => congrArg₂ List.cons (capture_value_eq code head) (capture_tuple_eq code tail)
termination_by structural _ _ _ _ related => related

omit [DecidableEq (Ty V S)] in
theorem related_key (code : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : lambdaKey code captureCode left = lambdaKey code captureCode right := by
  cases related <;> try rfl
  rename_i captures body
  simp only [lambdaKey, capture_tuple_eq captureCode captures, outer_profile code body]

omit [DecidableEq (Ty V S)] in
private theorem extend_keys {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {family : Family m} {args outs : Ports (Ty V S)}
    {root : m.Val (.value (.function args outs))} {keys : List (LambdaKey V S code.Key captureCode.Key)} {key : LambdaKey V S code.Key captureCode.Key}
    (earlier : ∀ {port : Ty V S} {value : m.Val port} {candidate : LambdaSummary V S code.Key captureCode.Key},
      family value → lambdaKey code captureCode value = some candidate → candidate ∈ keys.map LambdaKey.summary)
    (rootKey : lambdaKey code captureCode root = some key.summary) {port : Ty V S} {value : m.Val port} {candidate : LambdaSummary V S code.Key captureCode.Key}
    (known : WithExport family root value) (found : lambdaKey code captureCode value = some candidate) :
    candidate ∈ (key :: keys).map LambdaKey.summary := by
  cases known with
  | inherited earlierValue => exact List.mem_cons_of_mem _ (earlier earlierValue found)
  | exported =>
    rw [rootKey] at found
    cases found
    exact List.mem_cons_self

omit [DecidableEq (Ty V S)] in
theorem linked_extension (ordinary : OrdinaryOutputs Op)
    {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {familyL familyR : Family m} {prior : DispatchKeys V S code.Key captureCode.Key}
    (earlier : LinkedFamily primitives ids code captureCode familyL familyR prior)
    {args outs : Ports (Ty V S)} {left right : m.Val (.value (.function args outs))}
    {newL newR : LambdaKey V S code.Key captureCode.Key} (fresh : newL.Fresh prior.right ∧ newR.Fresh prior.left)
    (keyL : lambdaKey code captureCode left = some newL.summary) (keyR : lambdaKey code captureCode right = some newR.summary)
    (capturesL : TupleIn familyL (resolve m left).values) (capturesR : TupleIn familyR (resolve m right).values)
    (body : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    LinkedFamily primitives ids code captureCode (WithExport familyL left) (WithExport familyR right) (prior.addLambda newL newR) where
  checked :=
    { closedL := closed_export ordinary left earlier.ordinaryL earlier.checked.closedL capturesL
      closedR := closed_export ordinary right earlier.ordinaryR earlier.checked.closedR capturesR
      graphs := by
        intro _ _ _ _ knownL knownR related
        have same := related_key code captureCode related
        cases knownL with
        | inherited oldL =>
          cases knownR with
          | inherited oldR => exact earlier.checked.graphs oldL oldR related
          | exported => exact (fresh.2 (earlier.keysL oldL (same.trans keyR))).elim
        | exported =>
          cases knownR with
          | inherited oldR => exact (fresh.1 (earlier.keysR oldR (same.symm.trans keyL))).elim
          | exported => exact body }
  ordinaryL value plain := .inherited (earlier.ordinaryL value plain)
  ordinaryR value plain := .inherited (earlier.ordinaryR value plain)
  keysL := extend_keys earlier.keysL keyL
  keysR := extend_keys earlier.keysR keyR
  groupsL known found := by
    cases known with
    | inherited old => exact earlier.groupsL old found
    | exported => cases (lambda_has_no_memberProfile keyL).symm.trans found
  groupsR known found := by
    cases known with
    | inherited old => exact earlier.groupsR old found
    | exported => cases (lambda_has_no_memberProfile keyR).symm.trans found

omit [DecidableEq (Ty V S)] in
theorem linked_exports {code : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m} {familyL familyR : Family m} {prior : DispatchKeys V S code.Key captureCode.Key}
    (family : LinkedFamily primitives ids code captureCode familyL familyR prior)
    {args outs : Ports (Ty V S)} {left right : m.Val (.value (.function args outs))}
    (knownL : familyL left) (knownR : familyR right) : ExportAdmission primitives ids left right :=
  ⟨familyL, familyR, family.checked, knownL, knownR, fun values plain =>
    ⟨ordinary_tuple family.ordinaryL values plain, ordinary_tuple family.ordinaryR values plain⟩⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.AdmissionProofs
