module

public import Silmaril.Compiler.Explorer.Det.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Thms

/-!
# The deterministic specialisation: proofs

* `refines_of_valid`: a deterministic problem valid to its first return is refined in the
  generic, backward sense (`Problem.Refines` of `toProblem`): the machine's run is unique, it
  stops at the first return, so every reachable state lies on the path to it.
* `valid_of_segments`: valid edges of a mapping that starts at the entry and relates no return
  give `DetProblem.Valid` (the composition of `Silmaril.Compiler.CompilesTo.Sim`, kept to the
  first return).
* `edge_vacuous`: an edge at a point relating no states is valid.
* `Counterexample`: valid listed edges, no coverage, no valid problem and no refinement.
-/

@[expose] public section

namespace Silmaril.Proofs.Compiler.Explorer.Det

open Silmaril.Compiler.CompilesTo (Source Corr Seg Hop acc_transGen)
open Silmaril.Compiler.Explorer

variable {σ τ R : Type}

/-! ## Runs of a functional relation -/

theorem rtg_to_end {α : Type} {r : α → α → Prop} (hdet : ∀ a b c, r a b → r a c → b = c)
    {a y c : α} (hy : Relation.ReflTransGen r a y) (hend : ∀ z, ¬ r y z)
    (hc : Relation.ReflTransGen r a c) : Relation.ReflTransGen r c y := by
  induction hc with
  | refl => exact hy
  | tail _ hbc ih =>
    rcases Relation.ReflTransGen.cases_head ih with rfl | ⟨d, hbd, hdy⟩
    · exact absurd hbc (hend _)
    · rw [hdet _ _ _ hbc hbd]; exact hdy

theorem acc_of_rtg_end {α : Type} {r : α → α → Prop} (hdet : ∀ a b c, r a b → r a c → b = c)
    {c y : α} (hend : ∀ z, ¬ r y z) (h : Relation.ReflTransGen r c y) :
    Acc (fun t u => r u t) c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, fun z hz => absurd hz (hend z)⟩
  | head hcd _ ih => exact ⟨_, fun z hz => by rw [hdet _ _ _ hz hcd]; exact ih⟩

/-! ## The generic reading of a deterministic problem -/

section Bridge

variable (D : DetProblem σ τ R)

theorem step_det (x0 : τ) : ∀ a b c, D.Step x0 a b → D.Step x0 a c → b = c := by
  rintro a b c ⟨hb, -⟩ ⟨hc, -⟩
  rw [hb] at hc
  exact Option.some.inj hc

theorem proj {x0 : τ} {a : τ} {q : τ × τ}
    (h : Relation.ReflTransGen D.toProblem.tgt.step (x0, a) q) :
    q.1 = x0 ∧ Relation.ReflTransGen (D.Step x0) a q.2 := by
  induction h with
  | refl => exact ⟨rfl, .refl⟩
  | tail _ hst ih =>
    obtain ⟨h1, h2⟩ := hst
    exact ⟨h1.trans ih.1, ih.2.tail (ih.1 ▸ h2)⟩

theorem lift {x0 a b : τ} (h : Relation.ReflTransGen (D.Step x0) a b) :
    Relation.ReflTransGen D.toProblem.tgt.step (x0, a) (x0, b) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ⟨rfl, hst⟩

theorem refines_of_valid (h : D.Valid) : D.toProblem.Refines := by
  rintro s ⟨x0, x⟩ ⟨hx, he⟩ hsafe
  simp only at hx he
  subst x
  obtain ⟨t, r, y, hst, hfin, hrun, hret, hres⟩ := h x0 s he hsafe
  have hend : ∀ z, ¬ D.Step x0 y z := fun z hz => hz.2 hret
  have hon : ∀ q, Relation.ReflTransGen D.toProblem.tgt.step (x0, x0) q →
      q.1 = x0 ∧ Relation.ReflTransGen (D.Step x0) q.2 y := fun q hq =>
    ⟨(proj D hq).1, rtg_to_end (step_det D x0) hrun hend (proj D hq).2⟩
  -- a reachable state that is not the first return steps (to the next state of the path)
  have hmove : ∀ c, Relation.ReflTransGen (D.Step x0) c y → c = y ∨ ∃ d, D.Step x0 c d :=
    fun c hc => (Relation.ReflTransGen.cases_head hc).imp_right fun ⟨d, hd, _⟩ => ⟨d, hd⟩
  refine ⟨⟨fun ⟨q0, c⟩ hq hwrong => ?_, ?_⟩, fun ⟨q0, c⟩ hq hstuck => ?_,
    fun ⟨q0, c⟩ v hq hv => ?_⟩
  · obtain ⟨h1, h2⟩ := hon _ hq
    simp only at h1 h2
    subst h1
    rcases hmove c h2 with rfl | ⟨d, hd⟩
    · exact hwrong.2 hret
    · have := hd.1; rw [hwrong.1] at this; exact absurd this (by simp)
  · -- termination: every state on the path to the first return is accessible
    have key : ∀ c, Relation.ReflTransGen (D.Step x0) c y →
        Acc (fun a b => D.toProblem.tgt.step b a) (x0, c) := by
      intro c hc
      induction hc using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨_, fun q hq => absurd hq.2 (hend q.2)⟩
      | @head a d hcd _ ih =>
        refine ⟨_, fun q hq => ?_⟩
        obtain ⟨h1, h2⟩ := hq
        have e2 : q.2 = d := step_det D x0 a q.2 d h2 hcd
        have : q = (x0, d) := Prod.ext h1 e2
        rw [this]; exact ih
    exact key x0 hrun
  · obtain ⟨h1, h2⟩ := hon _ hq
    simp only at h1 h2
    subst h1
    rcases hmove c h2 with rfl | ⟨d, hd⟩
    · exact ⟨_, hret, rfl⟩
    · exact absurd ⟨rfl, hd⟩ (hstuck (q0, d))
  · obtain ⟨hf, rfl⟩ := hv
    obtain ⟨h1, h2⟩ := hon _ hq
    simp only at h1 h2 hf
    subst h1
    rcases hmove c h2 with rfl | ⟨d, hd⟩
    · exact ⟨t, r, hst, hfin, hres⟩
    · exact absurd hf hd.2

end Bridge

/-! ## Segments to the first return -/

theorem hop_steps {D : DetProblem σ τ R} (M : DetMapping D) {x0 x y : τ}
    (h : Hop M.corr.tgtStep (M.corr.tgtCut x0) x y) (hx : ¬ D.tgtFinal x0 x) :
    Relation.ReflTransGen (D.Step x0) x y := by
  induction h with
  | one h => exact .single ⟨h, hx⟩
  | more h hu _ ih => exact .head ⟨h, hx⟩ (ih fun hf => hu (.inr hf))

theorem valid_of_segments {D : DetProblem σ τ R} (M : DetMapping D) (hs : M.Starts)
    (hv : M.Valid) (hnf : M.NoReturnAtPoints) : D.Valid := by
  intro x0 s he hsafe
  obtain ⟨h0s, h0x, h0r⟩ := hs x0 s he
  have key : ∀ s, Acc (Relation.TransGen fun t u => D.src.step u t) s →
      ∀ k x, M.srcAt k s → M.tgtAt k x → M.rel k x0 s x → D.src.Safe s →
      ∃ t r y, Relation.ReflTransGen D.src.step s t ∧ D.src.final t r ∧
        Relation.ReflTransGen (D.Step x0) x y ∧ D.tgtFinal x0 y ∧ D.result x0 r y := by
    intro s hacc
    induction hacc with
    | intro s _ ih =>
      intro k x hs' hx hr hsafe'
      obtain ⟨t, y, hst, hxy, hnext⟩ := hv k x0 s x hs' hx hr hsafe'
      have hrun := hop_steps M hxy.1 (hnf k x0 s x hr)
      rcases hnext with ⟨j, htj, hyj, hrj⟩ | ⟨r, hfin, hyf, hres⟩
      · obtain ⟨u, r, z, h1, h2, h3, h4, h5⟩ :=
          ih t hst.1.swap j y htj hyj hrj (hsafe'.of_reaches hst.1.to_reflTransGen)
        exact ⟨u, r, z, hst.1.to_reflTransGen.trans h1, h2, hrun.trans h3, h4, h5⟩
      · exact ⟨t, r, y, hst.1.to_reflTransGen, hfin, hrun, hyf, hres⟩
  exact key s (acc_transGen hsafe.2) 0 x0 h0s h0x h0r hsafe

theorem edge_vacuous {D : DetProblem σ τ R} (M : DetMapping D) (k : Nat)
    (h : M.toMapping.Unrelated k) : M.EdgeValid k := by
  intro x0 s x hs hx hr _
  exact absurd hr (h s (x0, x) hs hx)

theorem starts_iff {D : DetProblem σ τ R} (M : DetMapping D) : M.toMapping.Starts → M.Starts :=
  fun h x0 s he => h s (x0, x0) ⟨rfl, he⟩

/-! ## The counterexample -/

namespace Counterexample

/-- Source: `0 → 1 → 2`, final at `2`, never wrong. -/
def src : Source Nat Unit where
  step s t := (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2)
  wrong _ := False
  final s _ := s = 2

/-- Target: `0 → 1 → 1 → …`: it never returns. -/
def tgt (x : Nat) : Option Nat := if x ≤ 1 then some 1 else none

/-- The problem: enter at `0` on both sides; the target returns at `2`. -/
def problem : DetProblem Nat Nat Unit where
  src := src
  tgt := tgt
  entry x0 s := x0 = 0 ∧ s = 0
  tgtFinal _ x := x = 2
  result _ _ _ := True

/-- The mapping: points `0` and `1` are the states `0` and `1` on both sides. -/
def mapping : DetMapping problem where
  srcAt k s := s = k
  tgtAt k x := x = k
  rel k _ s x := k ≤ 1 ∧ s = k ∧ x = k

theorem starts : mapping.Starts := by
  rintro x0 s ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, by decide, rfl, rfl⟩

theorem edge0 : mapping.EdgeValid 0 := by
  rintro x0 s x rfl rfl ⟨-, -, -⟩ -
  refine ⟨1, 1, ⟨.single (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨1, rfl⟩⟩,
    ⟨.one (by rfl), Or.inl ⟨1, rfl⟩⟩, Or.inl ⟨1, rfl, rfl, by decide, rfl, rfl⟩⟩

theorem not_covers : ¬ mapping.toMapping.Covers [0] := fun h =>
  h 1 (by simp) 1 (0, 1) rfl rfl ⟨by decide, rfl, rfl⟩

theorem safe0 : src.Safe 0 := by
  refine ⟨fun _ _ h => h, ?_⟩
  have a2 : Acc (fun t u => src.step u t) 2 :=
    ⟨_, fun y h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h⟩
  have a1 : Acc (fun t u => src.step u t) 1 :=
    ⟨_, fun y h => by
      rcases h with ⟨h, _⟩ | ⟨-, rfl⟩
      · cases h
      · exact a2⟩
  exact ⟨_, fun y h => by
    rcases h with ⟨-, rfl⟩ | ⟨h, _⟩
    · exact a1
    · cases h⟩

theorem reach_le_one {y : Nat} (h : Relation.ReflTransGen (problem.Step 0) 0 y) : y ≤ 1 := by
  induction h with
  | refl => decide
  | tail _ hst ih =>
    have := hst.1
    simp only [problem, tgt, ih, ite_true, Option.some.injEq] at this
    omega

theorem not_valid : ¬ problem.Valid := by
  intro h
  obtain ⟨_, _, y, _, _, hy, hfin, _⟩ := h 0 0 ⟨rfl, rfl⟩ safe0
  have := reach_le_one hy
  simp only [problem] at hfin
  omega

theorem acc_loop {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) (hr : r a a) : False := by
  induction h with
  | intro a _ ih => exact ih a hr hr

theorem not_refines : ¬ problem.toProblem.Refines := by
  intro h
  obtain ⟨⟨-, hacc⟩, -, -⟩ := h 0 (0, 0) ⟨rfl, rfl, rfl⟩ safe0
  have step : ∀ a, a ≤ 1 → problem.toProblem.tgt.step (0, a) (0, 1) := fun a ha =>
    ⟨rfl, by simp [problem, tgt, ha], by simp [problem]; omega⟩
  have hacc1 := hacc.inv (step 0 (by decide))
  exact acc_loop hacc1 (step 1 (by decide))

end Counterexample

end Silmaril.Proofs.Compiler.Explorer.Det

end
