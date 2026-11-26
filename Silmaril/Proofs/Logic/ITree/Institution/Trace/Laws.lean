module

public import Silmaril.Logic.ITree.Institution.Trace.Defs

public section

namespace Silmaril.Logic.ITree.TraceInstitution.Proofs

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

variable {S T U : TraceSignature.{u}}

theorem translate_id (φ : Sentence.{u,v} S) : φ.translate (𝟙 S) = φ := by
  rcases φ with ⟨A, t, P⟩
  change Sentence.mk A ((𝟙 S.toSignature : S.toSignature ⟶ S.toSignature).tree id t) _ = _
  rw [Signature.Hom.tree_id]
  congr 1
  funext p
  simp

theorem accepts_translate_comp (f : S ⟶ T) (g : T ⟶ U) (φ : Sentence.{u,v} S)
    (p : Trace U.toSignature.Event φ.Result) :
    (φ.translate (f ≫ g)).accepts p ↔ ((φ.translate f).translate g).accepts p := by
  change (∃ q, φ.accepts q ∧ (f ≫ g).trace q = p) ↔
    ∃ r, (∃ q, φ.accepts q ∧ f.trace q = r) ∧ g.trace r = p
  simp only [TraceSignature.Hom.trace_comp]
  exact ⟨fun ⟨q, h, eq⟩ => ⟨f.trace q, ⟨q, h, rfl⟩, eq⟩,
    fun ⟨_, ⟨q, h, rfl⟩, eq⟩ => ⟨q, h, eq⟩⟩

theorem translate_comp (f : S ⟶ T) (g : T ⟶ U) (φ : Sentence.{u,v} S) :
    φ.translate (f ≫ g) = (φ.translate f).translate g := by
  have ht := Signature.Hom.tree_comp f.hom g.hom id id φ.program
  have hp := funext fun p => propext (accepts_translate_comp f g φ p)
  exact congrArg₂ (Sentence.mk φ.Result) ht hp

theorem satisfaction_at (f : S ⟶ T) (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S)
    (x : M.State) : SatAt M (φ.translate f) x ↔ SatAt (M.reduct f.hom) φ x := by
  constructor
  · intro h p hp
    have ht := (f.handledTrace_image M.step x φ.program (f.trace p)).mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, eq⟩ := h (f.trace p) ht
    exact f.trace_injective eq ▸ hq
  · intro h p hp
    obtain ⟨q, hq, eq⟩ := (f.handledTrace_image M.step x φ.program p).mp hp
    exact ⟨q, h q hq, eq⟩

private theorem replay_renameState (M : Model.{u,w} S.toSignature) {Y : Type w} (e : M.State ≃ Y)
    (x : Y) {A : Type v} (p : Trace S.toSignature.Event A) :
    Replay (M.renameState e).step x p ↔ Replay M.step (e.symm x) p := by
  induction p generalizing x with
  | «prefix» | request | result => rfl
  | exchange ev r tail ih =>
    constructor
    · rintro ⟨y, hy, hp⟩
      exact ⟨e.symm y, hy, (ih y).mp hp⟩
    · rintro ⟨y, hy, hp⟩
      refine ⟨e y, ?_, (ih (e y)).mpr ?_⟩
      · simpa only [Model.renameState, Equiv.symm_apply_apply] using hy
      · rwa [e.symm_apply_apply]

theorem sat_renameState (M : Model.{u,w} S.toSignature) {Y : Type w} (e : M.State ≃ Y)
    (φ : Sentence.{u,v} S) : Sat (M.renameState e) φ ↔ Sat M φ := by
  have transfer (x : Y) : SatAt (M.renameState e) φ x ↔ SatAt M φ (e.symm x) :=
    forall_congr' fun p => imp_congr (and_congr_right fun _ => replay_renameState M e x p) Iff.rfl
  constructor
  · intro h x hx
    simpa only [Equiv.symm_apply_apply] using (transfer (e x)).mp
      (h (e x) (by simpa only [Model.renameState, Equiv.symm_apply_apply] using hx))
  · exact fun h x hx => (transfer x).mpr (h (e.symm x) hx)

end Silmaril.Logic.ITree.TraceInstitution.Proofs
