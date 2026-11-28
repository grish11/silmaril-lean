module

public import Silmaril.SSA.SeaOfNodes.GVN.Pass.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Pass
open Diamond (Dataflow Model Signature Ty Val ValueSort)
open Silmaril.SSA.RVSDG (Locals Origin Tuple)
open Elimination (Rewrite Routing inFinal)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

theorem mem_candidates (ref : Producer flow out) :
    ⟨out, ref⟩ ∈ candidates flow := by
  induction ref with
  | here => exact List.mem_cons_self
  | later ref ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨_, ref⟩, ih, rfl⟩)

private theorem before_final {t : Ty Data} (candidate : Producer flow out)
    (wire : Origin args past t) : inFinal candidate (before candidate wire) = keepOrigin flow wire := by
  induction candidate with
  | here => rfl
  | later ref ih => exact ih (weaken _ wire)

private theorem replacement_exists (candidate representative : Producer flow out)
    (earlier : Discovery.position representative < Discovery.position candidate) :
    ∃ wire, replacement? candidate representative = some wire ∧
      inFinal candidate wire = representative.origin := by
  induction candidate with
  | here => exact False.elim (Nat.not_lt_zero _ earlier)
  | @later past sigs ins head out op inputs rest ref ih =>
    cases representative with
    | here =>
      exact ⟨_, rfl, before_final ref (newest (past := past) .head)⟩
    | later prior =>
      exact ih prior (Nat.lt_of_succ_lt_succ earlier)

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

theorem eliminateCandidate_none_iff (candidate : Producer flow out) :
    eliminateCandidate? candidate = none ↔ Discovery.findRepresentative? candidate = none := by
  cases found : Discovery.findRepresentative? candidate with
  | none => simp [eliminateCandidate?, found]
  | some representative =>
    have listed : representative ∈ Discovery.earlier candidate := List.mem_of_find?_eq_some found
    obtain ⟨wire, replacement, address⟩ := replacement_exists candidate representative
      ((Discovery.mem_earlier_iff candidate representative).1 listed)
    have accepted := Discovery.findRepresentative?_sound candidate representative found
    simp [eliminateCandidate?, found, replacement, Elimination.eliminate?, accepted, address]

theorem step_none_iff (flow : Dataflow Op args past sigs) :
    step? flow = none ↔ NoDuplicate flow := by
  simp only [step?, List.findSome?_eq_none_iff]
  constructor
  · intro none sort candidate
    exact (Discovery.findRepresentative?_eq_none_iff candidate).1
      ((eliminateCandidate_none_iff candidate).1 (none ⟨sort, candidate⟩ (mem_candidates candidate)))
  · intro normal ⟨sort, candidate⟩ _
    exact (eliminateCandidate_none_iff candidate).2
      ((Discovery.findRepresentative?_eq_none_iff candidate).2 (normal sort candidate))

theorem eliminateCandidate_checked (candidate : Producer flow out) {result : Rewrite Op args past sigs}
    (accepted : eliminateCandidate? candidate = some result) :
    ∃ (representative : Producer flow out) (wire : Origin args (Elimination.operandScope candidate) (.value out)),
      Discovery.findRepresentative? candidate = some representative ∧
        replacement? candidate representative = some wire ∧
        Elimination.eliminate? candidate representative wire = some result := by
  cases rep : Discovery.findRepresentative? candidate with
  | none => simp [eliminateCandidate?, rep] at accepted
  | some representative =>
    cases source : replacement? candidate representative with
    | none => simp [eliminateCandidate?, rep, source] at accepted
    | some wire =>
      exact ⟨representative, wire, rfl, source, by simpa [eliminateCandidate?, rep, source] using accepted⟩

private theorem step_elimination {result : Rewrite Op args past sigs}
    (accepted : step? flow = some result) :
    ∃ (sort : ValueSort Data) (candidate representative : Producer flow sort)
      (wire : Origin args (Elimination.operandScope candidate) (.value sort)),
      Elimination.eliminate? candidate representative wire = some result := by
  obtain ⟨⟨sort, candidate⟩, _, found⟩ := List.exists_of_findSome?_eq_some accepted
  obtain ⟨representative, wire, _, _, checked⟩ := eliminateCandidate_checked candidate found
  exact ⟨sort, candidate, representative, wire, checked⟩

theorem step_size {result : Rewrite Op args past sigs} (accepted : step? flow = some result) :
    result.sigs'.length + 1 = sigs.length := by
  obtain ⟨_, candidate, representative, wire, checked⟩ := step_elimination accepted
  exact Elimination.eliminate_size candidate representative wire checked

private theorem run_none (fuel : Nat) (found : step? flow = none) :
    run (fuel + 1) flow = unchanged flow := by
  simp only [run, found]

private theorem run_some (fuel : Nat) {first : Rewrite Op args past sigs}
    (found : step? flow = some first) :
    run (fuel + 1) flow =
      ⟨compose first (run fuel first.flow).rewrite, (run fuel first.flow).deletions + 1⟩ := by
  simp only [run, found]

variable (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
variable (locals : Locals (Val m.value) past)

theorem step_sound {result : Rewrite Op args past sigs} (accepted : step? flow = some result) :
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) := by
  obtain ⟨_, candidate, representative, wire, checked⟩ := step_elimination accepted
  exact Elimination.eliminate_sound candidate representative wire m entry locals checked

theorem run_sound (fuel : Nat) (flow : Dataflow Op args past sigs) :
    let result := run fuel flow
    Routing.Agrees result.rewrite.route m entry (flow.eval m entry locals)
      (result.rewrite.flow.eval m entry locals) := by
  induction fuel generalizing sigs with
  | zero => exact fun _ _ => rfl
  | succ fuel ih =>
    cases found : step? flow with
    | none =>
      rw [run_none fuel found]
      exact fun _ _ => rfl
    | some first =>
      have firstEq := step_sound m entry locals found
      have tailEq := ih first.flow
      rw [run_some fuel found]
      exact fun t wire => (firstEq t wire).trans (tailEq t (first.route wire))

theorem run_progress (fuel : Nat) (flow : Dataflow Op args past sigs) :
    let result := run fuel flow
    result.rewrite.sigs'.length + result.deletions = sigs.length ∧ result.deletions ≤ fuel := by
  induction fuel generalizing sigs with
  | zero => simp [run, unchanged]
  | succ fuel ih =>
    cases found : step? flow with
    | none => simp [run, found, unchanged]
    | some first =>
      obtain ⟨count, budget⟩ := ih first.flow
      have removed := step_size found
      simp only [run, found, compose]
      omega

theorem run_normal_of_remaining (fuel : Nat) (flow : Dataflow Op args past sigs)
    (remaining : (run fuel flow).deletions < fuel) :
    NoDuplicate (run fuel flow).rewrite.flow := by
  induction fuel generalizing sigs with
  | zero => exact False.elim (Nat.not_lt_zero _ remaining)
  | succ fuel ih =>
    cases found : step? flow with
    | none =>
      rw [run_none fuel found]
      exact (step_none_iff flow).1 found
    | some first =>
      rw [run_some fuel found] at remaining ⊢
      exact ih first.flow (Nat.lt_of_succ_lt_succ remaining)

theorem normalize_normal (flow : Dataflow Op args past sigs) :
    NoDuplicate (normalize flow).rewrite.flow := by
  have count := (run_progress (sigs.length + 1) flow).1
  exact run_normal_of_remaining (sigs.length + 1) flow (by omega)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass
