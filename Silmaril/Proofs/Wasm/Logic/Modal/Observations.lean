module

public import Silmaril.Wasm.Logic.Modal.Defs
public import Silmaril.Logic.Institution.Borrowing

import Lean

@[expose] public section
namespace Silmaril.Logic.Modal.Wasm
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
variable {H : Type} {P : Profile} {host : HostSemantics H} {S T : Modal.Signature}

/-- Structural comparison of two independently defined evaluations, at every configuration. -/
theorem holds_toModal (M : Model P host S) (p : Modal.Formula S) (c : Config H) :
    Holds M p c ↔ p.Holds (toModal M) c := by
  induction p generalizing c with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp c) (hq c)
  | box p hp => exact forall_congr' fun d => imp_congr_right fun _ => hp d

theorem sat_toModal (M : Model P host S) (p : Modal.Formula S) :
    Sat M p ↔ Modal.Sat (toModal M) p := holds_toModal M p M.point

/-- Native truth is invariant under the full bounded operational model maps. -/
theorem holds_hom {M N : Model P host S} (h : M ⟶ N) (p : Modal.Formula S) (c : Config H) :
    Holds M p c ↔ Holds N p (h.map c) :=
  (holds_toModal M p c).trans ((p.holds_hom h c).trans (holds_toModal N p (h.map c)).symm)

theorem sat_hom {M N : Model P host S} (h : M ⟶ N) (p : Modal.Formula S) :
    Sat M p ↔ Sat N p :=
  (sat_toModal M p).trans
    ((Modal.sat_hom h p).trans (sat_toModal N p).symm)

/-- The native evaluation satisfies atom-renaming invariance in its own right. -/
theorem holds_map (f : S ⟶ T) (M : Model P host T) (p : Modal.Formula S) (c : Config H) :
    Holds M (p.map f) c ↔ Holds ((reduct f).obj M) p c := by
  induction p generalizing c with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp c) (hq c)
  | box p hp => exact forall_congr' fun d => imp_congr_right fun _ => hp d

/-- Model reducts commute on objects and all bounded morphisms. -/
theorem modalModels_natural (f : S ⟶ T) :
    reduct (P := P) (host := host) f ⋙ modalModels P host S =
      modalModels P host T ⋙ Modal.reduct f := rfl

/-- A genuine observation institution, whose truth is the native recursive evaluation. -/
def institution (P : Profile) (host : HostSemantics H) : Modal.Signature ⥤ Room where
  obj S := ⟨Modal.Formula S, Cat.of (Model P host S), Sat⟩
  map f := ⟨Modal.Formula.map f, reduct f, fun M p => holds_map f M p M.point⟩
  map_id _ := Room.hom_ext (funext Modal.Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Modal.Formula.map_comp f g)) rfl

/-- Restrict arbitrary K frames to the actual fixed Wasm execution frame. -/
def restrictionNatural (P : Profile) (host : HostSemantics H) :
    Modal.institution ⟶ institution P host where
  app S := ⟨id, modalModels P host S, sat_toModal⟩
  naturality := by
    intro S T f
    exact Room.hom_ext rfl (modalModels_natural f).symm

/-- Sentences go forwards unchanged; operational models reduce to Kripke models. -/
def restrictModal (P : Profile) (host : HostSemantics H) :
    Inst.CoHom ⟨Modal.Signature, Modal.institution⟩ ⟨Modal.Signature, institution P host⟩ :=
  ⟨𝟭 _, restrictionNatural P host⟩

/-- An actual-execution witness is also an unrestricted K witness. -/
theorem modal_satisfiable_of_execution (p : Modal.Formula S)
    (h : ∃ M : Model P host S, Sat M p) : ∃ M : Modal.Model S, Modal.Sat M p := by
  obtain ⟨M, hp⟩ := h
  exact ⟨toModal M, (sat_toModal M p).mp hp⟩

/-- K-unsatisfiability transfers to the actual-execution restriction. -/
theorem execution_unsatisfiable_of_modal (p : Modal.Formula S)
    (h : ¬ ∃ M : Modal.Model S, Modal.Sat M p) : ¬ ∃ M : Model P host S, Sat M p :=
  fun hp => h (modal_satisfiable_of_execution p hp)

/-- Consequence transfers in the restriction direction, without model expansiveness. -/
theorem execution_entails_of_modal (Γ : Set (Modal.Formula S)) (p : Modal.Formula S)
    (h : (Modal.institution.obj S).Entails Γ p) :
    ((institution P host).obj S).Entails Γ p := by
  intro M hΓ
  apply (sat_toModal M p).mpr
  exact h (toModal M) (fun q hq => (sat_toModal M q).mp (hΓ q hq))

/-- This is existential one-step execution, not reflexive-transitive reachability. -/
theorem diamond_iff (M : Model P host S) (p : Modal.Formula S) (c : Config H) :
    Holds M (diamond p) c ↔ ∃ d, Step P host c d ∧ Holds M p d := by
  classical
  change (¬ ∀ d, Step P host c d → ¬ Holds M p d) ↔ _
  constructor
  · intro h
    exact Classical.byContradiction fun absent =>
      h (fun d hd hp => absent ⟨d, hd, hp⟩)
  · rintro ⟨d, hd, hp⟩ h
    exact h d hd hp

/-- Every immediate successor is considered by the native distribution law. -/
theorem axiom_K (M : Model P host S) (p q : Modal.Formula S) (c : Config H) :
    Holds M (.imp (.box (.imp p q)) (.imp (.box p) (.box q))) c := by
  intro hpq hp d hd
  exact hpq d hd (hp d hd)

/- Dependency ceilings reject incomplete proofs or additional assumptions. -/
run_elab do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``holds_toModal, ``holds_hom, ``holds_map, ``modalModels_natural, ``restrictModal, ``modal_satisfiable_of_execution, ``execution_unsatisfiable_of_modal, ``execution_entails_of_modal, ``diamond_iff, ``axiom_K] do
    for axiomName in (← Lean.collectAxioms name) do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom in Wasm modal observations"

end Silmaril.Logic.Modal.Wasm
