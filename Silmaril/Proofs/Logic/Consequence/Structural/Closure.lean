module

public import Silmaril.Logic.Consequence.Structural.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Structural.Thms`: the inductive closure is the least
closed relation above its base. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Structural

open Silmaril.Consequence.Structural

universe u

variable {C : Type u}

theorem derives_closed (rs : Rules C) (R : Rel C) : Closed rs (Derives rs R) where
  refl h _ _ hc := .refl h hc
  weak _ _ _ hw hd := .weak hw hd
  cut h ps _ hps hd := .cut ps h hps hd

theorem derives_least {rs : Rules C} {R S : Rel C} (hRS : R ≤ S) (hS : Closed rs S) :
    Derives rs R ≤ S := by
  intro Γ c hd
  induction hd with
  | base h => exact hRS _ _ h
  | refl h hc => exact hS.refl h hc
  | weak hw _ ih => exact hS.weak hw ih
  | cut ps h _ _ ihps ih => exact hS.cut h (fun p hp => ihps p hp) ih

theorem closed_inf {rs : Rules C} (Rs : Set (Rel C)) (h : ∀ R ∈ Rs, Closed rs R) :
    Closed rs (sInf Rs) where
  refl hr Γ c hc := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall]
    exact fun R hR => (h R hR).refl hr hc
  weak Γ Δ c hw hd := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall] at hd ⊢
    exact fun R hR => (h R hR).weak hw (hd R hR)
  cut hc ps c hps hd := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall] at hps hd ⊢
    exact fun R hR => (h R hR).cut hc (fun p hp => hps p hp R hR) (hd R hR)

theorem derives_mono_rules {rs rs' : Rules C} (hr : rs.refl → rs'.refl) (hw : rs.weak ≤ rs'.weak)
    (hc : rs.cut → rs'.cut) (R : Rel C) : Derives rs R ≤ Derives rs' R := by
  intro Γ c hd
  induction hd with
  | base h => exact .base h
  | refl h hm => exact .refl (hr h) hm
  | weak h _ ih => exact .weak (hw _ _ h) ih
  | cut ps h _ _ ihps ih => exact .cut ps (hc h) (fun p hp => ihps p hp) ih

/-- Single cut from multi-cut and reflexivity. -/
theorem cut_single {R : Rel C} (hr : Reflexive R) (hc : Cut R) {Γ Δ : List C} {a c : C}
    (ha : R Γ a) (hd : R (a :: Δ) c) : R (Γ ++ Δ) c := by
  have h := @hc ((Γ, a) :: Δ.map fun d => ([d], d)) c (by
    simp only [List.mem_cons, List.mem_map]
    rintro p (rfl | ⟨d, hd, rfl⟩)
    · exact ha
    · exact hr (List.mem_singleton_self d)) (by simpa [Function.comp_def] using hd)
  have e : (Δ.map fun d => ([d], d)).flatMap Prod.fst = Δ := by
    clear hd h; induction Δ <;> simp_all
  simpa [e] using h

/-- Cut with a shared context, from multi-cut and weakening along list inclusion. -/
theorem cut_shared {R : Rel C} (hc : Cut R) (hw : WeakSubset R) {Γ cs : List C} {c : C}
    (hcs : ∀ a ∈ cs, R Γ a) (hd : R cs c) : R Γ c := by
  have h := @hc (cs.map fun a => (Γ, a)) c (by simpa using hcs)
    (by simpa [Function.comp_def] using hd)
  refine hw ?_ h
  intro x hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp
  exact hx

theorem weakSubperm_iff {R : Rel C} : WeakSubperm R ↔ WeakSublist R ∧ Exchange R := by
  constructor
  · intro h
    exact ⟨fun _ _ _ hs hd => h hs.subperm hd, fun _ _ _ hp hd => h hp.subperm hd⟩
  · rintro ⟨hs, he⟩ Γ Δ c ⟨Γ', hp, hsub⟩ hd
    exact hs hsub (he hp.symm hd)

end Silmaril.Proofs.Logic.Consequence.Structural
