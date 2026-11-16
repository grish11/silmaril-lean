module

public import Silmaril.Logic.HybridPolyadic.Modal.Defs

@[expose] public section
namespace Silmaril.Logic.HybridPolyadic
open CategoryTheory Silmaril.Logic.Institution

/-- The unary dual box ranges over the actual accessible worlds. -/
theorem Formula.holds_unaryBox {S : Signature} (M : Model S) {n : ℕ}
    (a : S.Action 1) (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    (p.unaryBox a).Holds M env w ↔
      ∀ v, M.relation 1 a w (fun _ => v) → p.Holds M env v := by
  classical
  constructor
  · intro h v hv
    by_contra hp
    exact h ⟨fun _ => v, hv, fun _ => hp⟩
  · intro h ⟨vs, hv, hs⟩
    have hvs : (fun _ : Fin 1 => vs 0) = vs := by
      funext i
      rw [Fin.eq_zero i]
    exact hs 0 (h (vs 0) (by rw [hvs]; exact hv))

theorem encodeModal_holds {S : Modal.Signature} (M : Model (modalSignatures.obj S))
    {n : ℕ} (p : Modal.Formula S) (env : Fin n → M.World) (w : M.World) :
    (encodeModal p).Holds M env w ↔ p.Holds ((modalReduct S).obj M) w := by
  induction p generalizing w with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp w) (hq w)
  | box p hp =>
    rw [encodeModal, Formula.holds_unaryBox]
    exact forall_congr' fun v => imp_congr_right fun _ => hp v

theorem encodeModal_map {S T : Modal.Signature} (f : S ⟶ T) {n : ℕ} (p : Modal.Formula S) :
    (encodeModal (n := n) p).map (modalSignatures.map f) = encodeModal (p.map f) := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact congrArg₂ Formula.imp hp hq
  | box p hp =>
    change Formula.imp (.dia modalAction (fun _ => Formula.imp _ .bot)) .bot = _
    exact congrArg (fun t => Formula.imp (.dia modalAction (fun _ => Formula.imp t .bot)) .bot) hp

/-- Satisfaction is proved, not supplied by the source graph's arrow. -/
def modalCorridor (S : Modal.Signature) : Modal.institution.obj S ⟶ institution.obj (modalSignatures.obj S) :=
  ⟨encodeModal, modalReduct S, fun M p => encodeModal_holds M p Fin.elim0 M.point⟩

def modalNatural : Modal.institution ⟶ modalSignatures ⋙ institution where
  app := modalCorridor
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (fun p => (encodeModal_map f p).symm)) rfl

/-- A genuine shared institution comorphism from normal K into hybrid/polyadic logic. -/
def modalToHybridPolyadic : Inst.CoHom ⟨Modal.Signature, Modal.institution⟩ inst :=
  ⟨modalSignatures, modalNatural⟩

@[simp] theorem modalReduct_expand {S : Modal.Signature} (M : Modal.Model S) :
    (modalReduct S).obj (expandModal M) = M := by
  cases M
  rfl

/-- Model-expansiveness needs object expansions, not a lift of arbitrary K arrows. -/
theorem modalCorridor_modelExpansive (S : Modal.Signature) :
    Corridor.ModelExpansive (modalCorridor S) :=
  fun M => ⟨expandModal M, modalReduct_expand M⟩

theorem modalToHybridPolyadic_modelExpansive :
    ∀ S, Corridor.ModelExpansive (modalToHybridPolyadic.ρ.app S) :=
  modalCorridor_modelExpansive

/-- The inclusion preserves and reflects the existence of a pointed model. -/
theorem modal_sat_iff {S : Modal.Signature} (p : Modal.Formula S) :
    (∃ M : Modal.Model S, Modal.Sat M p) ↔
      ∃ M : Model (modalSignatures.obj S), Sat M (encodeModal p) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨expandModal M, ?_⟩
    exact (encodeModal_holds (expandModal M) p Fin.elim0 M.point).mpr
      (by change Modal.Sat ((modalReduct S).obj (expandModal M)) p
          rw [modalReduct_expand]
          exact h)
  · rintro ⟨M, h⟩
    exact ⟨(modalReduct S).obj M, (encodeModal_holds M p Fin.elim0 M.point).mp h⟩

theorem modal_unsat_iff {S : Modal.Signature} (p : Modal.Formula S) :
    (¬ ∃ M : Modal.Model S, Modal.Sat M p) ↔
      ¬ ∃ M : Model (modalSignatures.obj S), Sat M (encodeModal p) :=
  not_congr (modal_sat_iff p)

/-- Semantic consequence can be used in either presentation. -/
theorem modal_entails_iff (S : Modal.Signature) (H : Set (Modal.Formula S))
    (p : Modal.Formula S) :
    (Modal.institution.obj S).Entails H p ↔
      (institution.obj (modalSignatures.obj S)).Entails (encodeModal '' H) (encodeModal p) :=
  by
    constructor
    · intro h M hM
      change Model (modalSignatures.obj S) at M
      apply (encodeModal_holds M p Fin.elim0 M.point).mpr
      apply h ((modalReduct S).obj M)
      intro q hq
      exact (encodeModal_holds M q Fin.elim0 M.point).mp (hM _ ⟨q, hq, rfl⟩)
    · intro h M hM
      change Modal.Model S at M
      have ht : Sat (expandModal M) (encodeModal p) := by
        apply h (expandModal M)
        rintro _ ⟨q, hq, rfl⟩
        apply (encodeModal_holds (expandModal M) q Fin.elim0 M.point).mpr
        change Modal.Sat ((modalReduct S).obj (expandModal M)) q
        rw [modalReduct_expand]
        exact hM q hq
      have hp := (encodeModal_holds (expandModal M) p Fin.elim0 M.point).mp ht
      change Modal.Sat ((modalReduct S).obj (expandModal M)) p at hp
      rw [modalReduct_expand] at hp
      exact hp

end Silmaril.Logic.HybridPolyadic
