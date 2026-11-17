module

public import Silmaril.Compiler.Explorer.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Thms

/-!
# Compilation problems and segment mappings: proofs

The proofs behind `Silmaril.Compiler.Explorer.Thms`: a valid mapping that starts at the entry
proves its problem (through `Corr.whole_of_segments`), coverage turns listed edges into a valid
mapping, the monotonicity of validity, the algebra of comorphism-generated relations, and a
counterexample showing that valid listed edges do not make a valid mapping.
-/

@[expose] public section

namespace Silmaril.Proofs.Compiler.Explorer

open Silmaril.Compiler.CompilesTo (Source Corr Seg Hop)
open Silmaril.Compiler.Explorer

variable {σ τ R : Type}

theorem valid_of_mapping {P : Problem σ τ R} (M : Mapping P) (hs : M.Starts) (hv : M.Valid) :
    P.Valid := by
  intro x0 s he hsafe
  obtain ⟨h0s, h0x, h0r⟩ := hs x0 s he
  exact M.corr.whole_of_segments hv 0 x0 s x0 h0s h0x h0r hsafe

theorem valid_of_edges {P : Problem σ τ R} (M : Mapping P) (L : List Nat)
    (he : ∀ k ∈ L, M.EdgeValid k) (hc : M.Covers L) : M.Valid := by
  intro k
  by_cases hk : k ∈ L
  · exact he k hk
  · intro x0 s x hs hx hr _
    exact absurd hr (hc k hk x0 s x hs hx)

theorem valid_mono {P Q : Problem σ τ R} (hsrc : Q.src = P.src) (htgt : Q.tgt = P.tgt)
    (he : ∀ x0 s, Q.entry x0 s → P.entry x0 s)
    (hf : ∀ x0 y, P.tgtFinal x0 y → Q.tgtFinal x0 y)
    (hr : ∀ x0 r y, P.result x0 r y → Q.result x0 r y) (h : P.Valid) : Q.Valid := by
  intro x0 s hq hsafe
  rw [hsrc] at hsafe ⊢
  obtain ⟨t, r, y, h1, h2, h3, h4, h5⟩ := h x0 s (he x0 s hq) hsafe
  refine ⟨t, r, y, h1, h2, ?_, hf x0 y h4, hr x0 r y h5⟩
  have : Q.tgtStep = P.tgtStep := by
    funext a b; simp only [Problem.tgtStep, htgt]
  rw [this]; exact h3

section Comorphisms

variable {S T U V : Type} {A : ObsLogic S V} {B : ObsLogic T V} {C : ObsLogic U V}

theorem generated_comp (c : ObsComorphism A B) (d : ObsComorphism B C) (hB : B.Functional)
    {Φ : A.Obs → Prop} {s : S} {y : T} {x : U} (h₁ : c.Generated Φ s y)
    (h₂ : d.Generated (c.image Φ) y x) : (c.comp d).Generated Φ s x := by
  intro o ho
  obtain ⟨v, hs, hy⟩ := h₁ o ho
  obtain ⟨w, hy', hx⟩ := h₂ (c.map o) ⟨o, ho, rfl⟩
  exact ⟨v, hs, (hB _ _ _ _ hy hy') ▸ hx⟩

theorem generated_iff (c : ObsComorphism A B) (hA : A.Functional) (hB : B.Functional)
    {Φ : A.Obs → Prop} {s : S} {x : T} (h : c.Generated Φ s x) {o : A.Obs} (ho : Φ o) (v : V) :
    A.Holds s o v ↔ B.Holds x (c.map o) v := by
  obtain ⟨w, hs, hx⟩ := h o ho
  constructor
  · intro hv; exact (hA _ _ _ _ hs hv) ▸ hx
  · intro hv; exact (hB _ _ _ _ hx hv) ▸ hs

end Comorphisms

/-! ## The counterexample: valid listed edges, no valid mapping -/

namespace Counterexample

/-- Source: `0 → 1 → 2`, final at `2`, never wrong. -/
def src : Source Nat Unit where
  step s t := (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2)
  wrong _ := False
  final s _ := s = 2

/-- Target: `0 → 1 → 1 → …`: it never returns. -/
def tgt (x : Nat) : Option Nat := if x ≤ 1 then some 1 else none

/-- The problem: enter at `0` on both sides; the target returns at `2`. -/
def problem : Problem Nat Nat Unit where
  src := src
  tgt := tgt
  entry x0 s := x0 = 0 ∧ s = 0
  tgtFinal _ x := x = 2
  result _ _ _ := True

/-- The mapping: points `0` and `1` are the states `0` and `1` on both sides. -/
def mapping : Mapping problem where
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

theorem not_covers : ¬ mapping.Covers [0] := fun h =>
  h 1 (by simp) 0 1 1 rfl rfl ⟨by decide, rfl, rfl⟩

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

theorem reach_le_one {y : Nat} (h : Relation.ReflTransGen problem.tgtStep 0 y) : y ≤ 1 := by
  induction h with
  | refl => decide
  | tail _ hst ih =>
    simp only [Problem.tgtStep, problem, tgt, ih, ite_true, Option.some.injEq] at hst
    omega

theorem not_valid : ¬ problem.Valid := by
  intro h
  obtain ⟨_, _, y, _, _, hy, hfin, _⟩ := h 0 0 ⟨rfl, rfl⟩ safe0
  have := reach_le_one hy
  simp only [problem] at hfin
  omega

end Counterexample

end Silmaril.Proofs.Compiler.Explorer

end
