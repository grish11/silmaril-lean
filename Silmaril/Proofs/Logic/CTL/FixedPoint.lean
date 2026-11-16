module

public import Silmaril.Logic.CTL.Mu.Defs

@[expose] public section
namespace Silmaril.Logic.CTL

/-- Finite until paths are exactly the least fixed point of Q ∪ (P ∩ EX X). -/
theorem until_iff_lfp {W : Type} (R : W → W → Prop) (P Q : W → Prop)
    (F : Set W →o Set W)
    (hF : ∀ X w, w ∈ F X ↔ Q w ∨ (P w ∧ ∃ v, R w v ∧ v ∈ X)) (w : W) :
    Until R P Q w ↔ w ∈ F.lfp := by
  constructor
  · intro h
    induction h with
    | now hq => exact (congrArg (fun X => _ ∈ X) F.map_lfp).mp ((hF _ _).mpr (Or.inl hq))
    | next hp hr _ ih =>
        exact (congrArg (fun X => _ ∈ X) F.map_lfp).mp ((hF _ _).mpr (Or.inr ⟨hp, _, hr, ih⟩))
  · have hpre : F {x | Until R P Q x} ⊆ {x | Until R P Q x} := by
      intro x hx
      rcases (hF _ x).mp hx with hq | ⟨hp, v, hr, hu⟩
      · exact .now hq
      · exact .next hp hr hu
    exact fun hw => F.lfp_le hpre hw

/-- Infinite paths, rather than an assumed interpretation, characterize the greatest fixed point. -/
theorem globally_iff_gfp {W : Type} (R : W → W → Prop) (P : W → Prop)
    (F : Set W →o Set W)
    (hF : ∀ X w, w ∈ F X ↔ P w ∧ ∃ v, R w v ∧ v ∈ X) (w : W) :
    Globally R P w ↔ w ∈ F.gfp := by
  classical
  constructor
  · have hpost : {x | Globally R P x} ⊆ F {x | Globally R P x} := by
      intro x hx
      exact (hF _ x).mpr ((globally_unfold R P x).mp hx)
    exact fun hw => F.le_gfp hpost hw
  · intro hw
    have unfold (x : W) (hx : x ∈ F.gfp) : P x ∧ ∃ y, R x y ∧ y ∈ F.gfp :=
      (hF _ x).mp ((congrArg (fun X => x ∈ X) F.map_gfp).mpr hx)
    have successor (x : {x : W // x ∈ F.gfp}) :
        ∃ y : {y : W // y ∈ F.gfp}, R x.val y.val := by
      obtain ⟨y, hr, hy⟩ := (unfold x.val x.property).2
      exact ⟨⟨y, hy⟩, hr⟩
    choose next hnext using successor
    let path : Nat → {x : W // x ∈ F.gfp} := Nat.rec ⟨w, hw⟩ (fun _ x => next x)
    exact ⟨fun n => (path n).val, rfl, fun n => hnext (path n),
      fun n => (unfold (path n).val (path n).property).1⟩

end Silmaril.Logic.CTL
