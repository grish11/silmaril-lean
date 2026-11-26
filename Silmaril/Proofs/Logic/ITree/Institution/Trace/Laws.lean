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

theorem translateLift_eq (f : S ⟶ T) (φ : Sentence.{u,v} S) : φ.translateLift f.hom = φ.translate f := by
  unfold Sentence.translateLift Sentence.translate
  simp only [f.traceLift_iff]

theorem translateLift_id (φ : Sentence.{u,v} S) : φ.translateLift (𝟙 S.toSignature) = φ := by
  cases φ
  simp [Sentence.translateLift]

theorem translateLift_comp (f : S.toSignature ⟶ T.toSignature) (g : T.toSignature ⟶ U.toSignature)
    (φ : Sentence.{u,v} S) : φ.translateLift (f ≫ g) = (φ.translateLift f).translateLift g := by
  refine congrArg₂ (Sentence.mk φ.Result) (f.tree_comp g id id φ.program) (funext fun r => propext ?_)
  change (∃ p, φ.accepts p ∧ (f ≫ g).TraceLift p r) ↔
    ∃ q, (∃ p, φ.accepts p ∧ f.TraceLift p q) ∧ g.TraceLift q r
  constructor
  · rintro ⟨p, accepted, lift⟩
    obtain ⟨q, first, second⟩ := (f.traceLift_comp g p r).mp lift
    exact ⟨q, ⟨p, accepted, first⟩, second⟩
  · rintro ⟨q, ⟨p, accepted, first⟩, second⟩
    exact ⟨p, accepted, (f.traceLift_comp g p r).mpr ⟨q, first, second⟩⟩

theorem satisfaction_lift_at (f : S.toSignature ⟶ T.toSignature) (keys : Function.Injective f.request)
    (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S) (x : M.State) :
    SatAt M (φ.translateLift f) x ↔ SatAt (M.reduct f) φ x := by
  constructor
  · intro satisfied p handled
    obtain ⟨q, lift, seen⟩ := f.handledTrace_lift M.step x φ.program p handled
    obtain ⟨p', accepted, other⟩ := satisfied q seen
    exact f.traceLift_unique keys other lift ▸ accepted
  · intro satisfied q handled
    obtain ⟨p, lift, seen⟩ := f.handledTrace_project M.step x φ.program q handled
    exact ⟨p, satisfied p seen, lift⟩

theorem satisfaction_at (f : S ⟶ T) (M : Model.{u,w} T.toSignature) (φ : Sentence.{u,v} S)
    (x : M.State) : SatAt M (φ.translate f) x ↔ SatAt (M.reduct f.hom) φ x := by
  rw [← translateLift_eq f φ]
  exact satisfaction_lift_at f.hom f.request_injective M φ x

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

theorem valid_hasTrace_iff {A : Type v} (source target : Tree S.toSignature.Event A) :
    (∀ M : Model.{u, 0} S.toSignature, Sat M ⟨A, source, HasTrace target⟩) ↔ TraceLE source target := by
  let all : Model.{u, 0} S.toSignature := ⟨Unit, fun _ => True, fun _ _ _ _ => True⟩
  have replay (trace : Trace S.toSignature.Event A) : Replay all.step () trace := by
    induction trace with
    | «prefix» | request | result => trivial
    | exchange _ _ _ ih => exact ⟨(), trivial, ih⟩
  exact ⟨fun valid trace seen => valid all () trivial trace ⟨seen, replay trace⟩,
    fun included _ _ _ trace seen => included trace seen.1⟩

end Silmaril.Logic.ITree.TraceInstitution.Proofs
