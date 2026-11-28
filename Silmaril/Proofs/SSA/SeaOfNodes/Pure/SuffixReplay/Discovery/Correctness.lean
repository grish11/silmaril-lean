module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms
import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Routing operandScope routeSuffix erase)
open scoped Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
open Silmaril.SSA.SeaOfNodes.Pure
open Pure.ConstantFold
open Pure.SubZero (model word)
open Pure.SuffixReplay
open Pure.SuffixReplay.Discovery
open Silmaril.SSA.RVSDG (Origin Tuple)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {block : Block inputs ports} {candidate : Producer block.flow word} {edit : Edit block}

private theorem countLeftLiterals_le {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
    (flow : Dataflow SubZero.Opcode args past sigs) (known : RightSpine.Prefix args past) :
    countLeftLiterals known flow ≤ sigs.length := by
  induction flow with
  | nil => exact Nat.le_refl _
  | cons op operands rest ih =>
    have tail := ih (known.record op operands)
    simp only [countLeftLiterals, List.length_cons]
    split <;> omega

private theorem weight_lt_of_primary {before after : Block inputs ports}
    (less : primaryWeight after < primaryWeight before) : weight after < weight before := by
  let n := primaryWeight after
  have bound : leftLiteralCount after ≤ n :=
    Nat.le_trans (countLeftLiterals_le after.flow RightSpine.Prefix.empty) (Nat.le_add_right _ _)
  have square : (n + 1) * (n + 1) = n * n + n + n + 1 := by
    rw [Nat.mul_succ, Nat.succ_mul]
    omega
  calc
    weight after = n * n + leftLiteralCount after := rfl
    _ < (n + 1) * (n + 1) := by omega
    _ ≤ primaryWeight before * primaryWeight before := Nat.mul_self_le_mul_self less
    _ ≤ weight before := Nat.le_add_right _ _

private theorem checkedEdit_fields {rule : Rule} {state : State inputs ports block.sigs}
    (accepted : checkedEdit? block rule state = some edit) : edit.rule = rule ∧ edit.state = state := by
  by_cases valid : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length ∧
      Progress rule block state.block ∧ weight state.block < weight block
  · simp [checkedEdit?, valid] at accepted
    cases accepted
    exact ⟨rfl, rfl⟩
  · simp [checkedEdit?, valid] at accepted

theorem add?_checked (accepted : add? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      addRule? applied.rule = some edit.rule ∧ edit.state = fromRewrite block applied.rewrite := by
  cases checked : AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
  | error reason => simp [add?, checked] at accepted
  | ok result =>
    cases result with
    | none => simp [add?, checked] at accepted
    | some applied =>
      simp only [add?, checked, Option.bind_eq_some_iff] at accepted
      obtain ⟨rule, kind, hat⟩ := accepted
      obtain ⟨sameRule, sameState⟩ := checkedEdit_fields hat
      exact ⟨applied, rfl, sameRule ▸ kind, sameState⟩

theorem rightZero?_checked (accepted : rightZero? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      applied.rule = .rightZero ∧ edit.rule = .rightZero ∧ edit.state = fromRewrite block applied.rewrite := by
  obtain ⟨found, rule⟩ := Option.filter_eq_some_iff.mp accepted
  have isRightZero : edit.rule = .rightZero := of_decide_eq_true rule
  obtain ⟨applied, checked, kind, state⟩ := add?_checked found
  rw [isRightZero] at kind
  have selected : applied.rule = .rightZero := by
    cases picked : applied.rule <;> simp [addRule?, picked] at kind ⊢
  exact ⟨applied, checked, selected, isRightZero, state⟩

private theorem unused_agrees (accepted : unused? block candidate = some edit)
    (entry : Tuple (Val model.value) (dataPorts inputs)) : Agrees block edit.state entry := by
  obtain ⟨deleted, checked, admitted⟩ := Option.bind_eq_some_iff.mp accepted
  rw [(checkedEdit_fields admitted).2]
  exact ⟨Deletion.delete?_agrees checked model entry PUnit.unit, (Deletion.delete?_eq_some_iff.mp checked).2⟩

private theorem checkedEdit_erasure {rule : Rule} {state : State inputs ports block.sigs}
    (erases : rule.erases = true) (bindings : state.block.sigs.length + 1 = block.sigs.length)
    (kept : List.Sublist (Deletion.opcodes state.block.flow) (Deletion.opcodes block.flow)) :
    checkedEdit? block rule state ≠ none := by
  have adds : addCount state.block ≤ addCount block := kept.countP_le
  have primary : primaryWeight state.block < primaryWeight block := by
    unfold primaryWeight
    omega
  have progress : Progress rule block state.block := by
    have distinct : rule ≠ .literalRight := by
      intro same
      subst rule
      cases erases
    simpa [Progress, distinct] using primary
  simp [checkedEdit?, erases, bindings, progress, weight_lt_of_primary primary]

theorem unused?_eq_none_iff : unused? block candidate = none ↔
    Deletion.delete? candidate block.packet = none := by
  cases checked : Deletion.delete? candidate block.packet with
  | none => simp [unused?, checked]
  | some deleted =>
    let state : State inputs ports block.sigs :=
      ⟨⟨deleted.erasure.sigs', deleted.erasure.flow, deleted.outputs⟩, deleted.erasure.route⟩
    have kept : List.Sublist (Deletion.opcodes state.block.flow) (Deletion.opcodes block.flow) := by
      change List.Sublist (Deletion.opcodes deleted.erasure.flow) (Deletion.opcodes block.flow)
      rw [Deletion.delete?_opcode_order checked]
      exact List.eraseIdx_sublist _ _
    simp only [unused?, checked, Option.bind_some]
    change checkedEdit? block .deleteUnused state = none ↔ some deleted = none
    simp [checkedEdit_erasure (rule := .deleteUnused) rfl deleted.erasure.shorter kept]

section Opcodes

variable {args : List (Ty Unit)} {past sigs target : List (List (Ty Unit))}

private theorem routeSuffix_opcodes (flow : Dataflow SubZero.Opcode args past sigs)
    (route : Routing args past target) :
    Deletion.opcodes (routeSuffix flow route).1 = Deletion.opcodes flow := by
  induction flow generalizing target with
  | nil => rfl
  | @cons _ _ ins out opcode operands rest ih =>
    exact congrArg (List.cons ⟨ins, out, opcode⟩) (ih (route.push [.value out]))

private theorem erase_opcodes {flow : Dataflow SubZero.Opcode args past sigs} {sort : ValueSort Unit}
    (node : Producer flow sort) (wire : Origin args (operandScope node) (.value sort)) :
    List.Sublist (Deletion.opcodes (erase node wire).flow) (Deletion.opcodes flow) := by
  induction node with
  | @here past sigs ins out opcode operands rest =>
    change Origin args past (.value out) at wire
    change List.Sublist (Deletion.opcodes (routeSuffix rest (GVN.Elimination.dropNewest wire)).1)
      (⟨ins, out, opcode⟩ :: Deletion.opcodes rest)
    rw [routeSuffix_opcodes]
    exact List.sublist_cons_self _ _
  | later node ih => exact (ih wire).cons_cons _

end Opcodes

theorem reuseAdd?_checked (accepted : reuseAdd? block candidate = some edit) :
    ∃ rewrite, isAdd candidate.key.opcode = true ∧ GVN.Pass.eliminateCandidate? candidate = some rewrite ∧
      edit.rule = .reuseAdd ∧ edit.state = fromRewrite block rewrite := by
  by_cases add : isAdd candidate.key.opcode = true
  · simp only [reuseAdd?, add, ↓reduceIte, Option.bind_eq_some_iff] at accepted
    obtain ⟨rewrite, checked, admitted⟩ := accepted
    obtain ⟨rule, state⟩ := checkedEdit_fields admitted
    exact ⟨rewrite, add, checked, rule, state⟩
  · simp [reuseAdd?, add] at accepted

theorem reuseAdd?_eq_none_iff : reuseAdd? block candidate = none ↔
    isAdd candidate.key.opcode = false ∨
      ∀ representative : Producer block.flow word, GVN.checkRepresentative candidate representative = false := by
  cases add : isAdd candidate.key.opcode with
  | false => simp [reuseAdd?, add]
  | true =>
    simp only [reuseAdd?, add, ↓reduceIte, Bool.true_eq_false, false_or]
    rw [← GVN.Discovery.findRepresentative?_eq_none_iff, ← GVN.Pass.eliminateCandidate?_eq_none_iff]
    cases checked : GVN.Pass.eliminateCandidate? candidate with
    | none => simp
    | some rewrite =>
      obtain ⟨representative, wire, _, _, accept⟩ := GVN.Pass.eliminateCandidate?_checked candidate checked
      have bindings := GVN.Elimination.eliminate_size candidate representative wire accept
      have shape : erase candidate wire = rewrite := by
        unfold GVN.Elimination.eliminate? at accept
        split at accept
        · exact Option.some.inj accept
        · contradiction
      have kept : List.Sublist (Deletion.opcodes rewrite.flow) (Deletion.opcodes block.flow) := by
        rw [← shape]
        exact erase_opcodes candidate wire
      simp [checkedEdit_erasure (rule := .reuseAdd) (state := fromRewrite block rewrite) rfl bindings kept]

theorem step?_checked (accepted : step? block = some edit) :
    ∃ candidate : Producer block.flow word,
      add? block candidate = some edit ∨ reuseAdd? block candidate = some edit ∨ unused? block candidate = some edit := by
  cases found : (RightIdentityPass.wordProducers block.flow).findSome? (add? block) with
  | none =>
    cases reused : (RightIdentityPass.wordProducers block.flow).findSome? (reuseAdd? block) with
    | none =>
      have chosen : (RightIdentityPass.wordProducers block.flow).findSome? (unused? block) = some edit := by
        simpa [step?, found, reused] using accepted
      obtain ⟨candidate, _, checked⟩ := List.exists_of_findSome?_eq_some chosen
      exact ⟨candidate, .inr (.inr checked)⟩
    | some first =>
      have same : first = edit := by simpa [step?, found, reused] using accepted
      subst edit
      obtain ⟨candidate, _, checked⟩ := List.exists_of_findSome?_eq_some reused
      exact ⟨candidate, .inr (.inl checked)⟩
  | some first =>
    have same : first = edit := by simpa [step?, found] using accepted
    subst edit
    obtain ⟨candidate, _, checked⟩ := List.exists_of_findSome?_eq_some found
    exact ⟨candidate, .inl checked⟩

theorem step_agrees (accepted : step? block = some edit) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Agrees block edit.state entry := by
  obtain ⟨candidate, checked | checked | checked⟩ := step?_checked accepted
  · obtain ⟨applied, chosen, _, same⟩ := add?_checked checked
    rw [same]
    exact fromRewrite_agrees applied.rewrite entry (AddIdealize.step_agrees chosen entry)
  · obtain ⟨rewrite, _, chosen, _, same⟩ := reuseAdd?_checked checked
    rw [same]
    obtain ⟨representative, wire, _, _, accepted⟩ := GVN.Pass.eliminateCandidate?_checked candidate chosen
    exact fromRewrite_agrees rewrite entry
      (GVN.Elimination.eliminate_sound candidate representative wire model entry PUnit.unit accepted)
  · exact unused_agrees checked entry

private theorem mem_producers (candidate : Producer block.flow word) :
    candidate ∈ RightIdentityPass.wordProducers block.flow :=
  List.mem_filterMap.mpr ⟨⟨word, candidate⟩, GVN.Pass.mem_candidates candidate, rfl⟩

theorem step?_eq_none_iff (block : Block inputs ports) : step? block = none ↔ NoEligible block := by
  have scan_iff (check : Producer block.flow word → Option (Edit block)) :
      (RightIdentityPass.wordProducers block.flow).findSome? check = none ↔ ∀ candidate, check candidate = none :=
    ⟨fun miss candidate => List.findSome?_eq_none_iff.mp miss candidate (mem_producers candidate),
      fun miss => List.findSome?_eq_none_iff.mpr fun candidate _ => miss candidate⟩
  have noHit : step? block = none ↔
      (RightIdentityPass.wordProducers block.flow).findSome? (add? block) = none ∧
        (RightIdentityPass.wordProducers block.flow).findSome? (reuseAdd? block) = none ∧
        (RightIdentityPass.wordProducers block.flow).findSome? (unused? block) = none := by
    cases first : (RightIdentityPass.wordProducers block.flow).findSome? (add? block) <;>
      cases second : (RightIdentityPass.wordProducers block.flow).findSome? (reuseAdd? block) <;>
      simp [step?, first, second]
  rw [noHit, scan_iff, scan_iff, scan_iff]
  exact ⟨fun miss candidate => ⟨miss.1 candidate, miss.2.1 candidate, miss.2.2 candidate⟩,
    fun miss => ⟨fun candidate => (miss candidate).1,
      fun candidate => (miss candidate).2.1, fun candidate => (miss candidate).2.2⟩⟩

private theorem run_spec (fuel : Nat) (block : Block inputs ports) (enough : weight block < fuel) :
    let final := Discovery.run fuel block enough
    (final.state.block.sigs.length + final.rules.countP Rule.erases = block.sigs.length ∧
      weight final.state.block + final.rules.length ≤ weight block ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry := by
  induction fuel generalizing block with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel ih =>
    dsimp only [Discovery.run]
    split
    · rename_i missing
      exact ⟨⟨by simp [initial], by simp [initial], (step?_eq_none_iff block).mp missing⟩,
        fun entry => run_agrees (requests := []) rfl entry⟩
    · rename_i edit checked
      have size := edit.bindingCount
      have smaller := edit.decreases
      obtain ⟨⟨tailSize, tailBudget, stopped⟩, tailAgrees⟩ := ih edit.state.block (by omega)
      refine ⟨⟨?_, ?_, stopped⟩, fun entry => compose_agrees entry (step_agrees checked entry) (tailAgrees entry)⟩
      · simp only [State.compose, List.countP_cons]
        omega
      · simp only [State.compose, List.length_cons]
        omega

theorem normalize_spec (block : Block inputs ports) :
    let final := normalize block
    (final.state.block.sigs.length + final.rules.countP Rule.erases = block.sigs.length ∧
      weight final.state.block + final.rules.length ≤ weight block ∧ NoEligible final.state.block) ∧
      ∀ entry : Tuple (Val model.value) (dataPorts inputs), Agrees block final.state entry :=
  run_spec _ block (Nat.lt_succ_self _)

theorem literalRight_progress (selected : edit.rule = .literalRight) :
    edit.state.block.sigs.length = block.sigs.length ∧
      addCount edit.state.block = addCount block ∧ leftLiteralCount edit.state.block < leftLiteralCount block := by
  have count := edit.bindingCount
  have side := edit.progress
  simp [selected, Rule.erases] at count
  simp [Progress, selected] at side
  exact ⟨count, by unfold primaryWeight at side; omega, side.2⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery
