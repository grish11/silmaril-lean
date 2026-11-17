module

public import Silmaril.Compiler.Explorer.Defs
import Silmaril.Proofs.Compiler.Explorer.Basic

/-!
# Compilation problems and segment mappings: theorems

* `Problem.valid_of_mapping`: a valid mapping that starts at the entry proves the translation.
* `Mapping.valid_of_edges`: valid listed edges and coverage make a valid mapping.
* `Counterexample.edges_not_valid`: valid listed edges alone do not (no coverage, no valid
  translation).
* `Problem.Valid.mono`: validity survives a stronger entry convention and weaker observations.
* `ObsComorphism.generated_mono`, `generated_comp`, `generated_iff`: the relations comorphisms
  generate shrink with the observables, compose through a functional middle logic, and for
  functional logics determine the observed values.
* `Mapping.RefinesComorphism.observe`, `Mapping.ofComorphism_refines`,
  `Mapping.RefinesAt.mono`: what refinement of a generated relation gives.

Proofs: `Silmaril.Proofs.Compiler.Explorer.Basic`.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.Compiler.CompilesTo (Source)

variable {σ τ R : Type}

/-- **A valid mapping that starts at the entry proves the translation** (`Corr.whole_of_segments`
from point `0`). -/
theorem Problem.valid_of_mapping {P : Problem σ τ R} (M : Mapping P) (hs : M.Starts)
    (hv : M.Valid) : P.Valid :=
  Silmaril.Proofs.Compiler.Explorer.valid_of_mapping M hs hv

/-- **Valid listed edges and coverage make a valid mapping**: the segments of the points outside
`L` are vacuous. -/
theorem Mapping.valid_of_edges {P : Problem σ τ R} (M : Mapping P) (L : List Nat)
    (he : ∀ k ∈ L, M.EdgeValid k) (hc : M.Covers L) : M.Valid :=
  Silmaril.Proofs.Compiler.Explorer.valid_of_edges M L he hc

/-- **Validity is monotone**: with the same models, a stronger entry convention, a weaker return
condition and a weaker result relation keep a translation valid. -/
theorem Problem.Valid.mono {P Q : Problem σ τ R} (hsrc : Q.src = P.src) (htgt : Q.tgt = P.tgt)
    (he : ∀ x0 s, Q.entry x0 s → P.entry x0 s)
    (hf : ∀ x0 y, P.tgtFinal x0 y → Q.tgtFinal x0 y)
    (hr : ∀ x0 r y, P.result x0 r y → Q.result x0 r y) (h : P.Valid) : Q.Valid :=
  Silmaril.Proofs.Compiler.Explorer.valid_mono hsrc htgt he hf hr h

/-- **Valid listed edges do not make a valid mapping**: a problem and a mapping that starts at
the entry whose only listed edge (point `0`) is valid, whose listed points do not cover it, and
whose translation (hence the mapping) is not valid. -/
theorem Counterexample.edges_not_valid :
    ∃ (P : Problem Nat Nat Unit) (M : Mapping P), M.Starts ∧ (∀ k ∈ [0], M.EdgeValid k) ∧
      ¬ M.Covers [0] ∧ ¬ M.Valid ∧ ¬ P.Valid := by
  open Silmaril.Proofs.Compiler.Explorer.Counterexample in
  exact ⟨problem, mapping, starts, by simpa using edge0, not_covers,
    fun hv => not_valid (Problem.valid_of_mapping mapping starts hv), not_valid⟩

namespace ObsComorphism

variable {S T U V : Type} {A : ObsLogic S V} {B : ObsLogic T V} {C : ObsLogic U V}

/-- Fewer observables, a weaker generated relation. -/
theorem generated_mono (c : ObsComorphism A B) {Φ Ψ : A.Obs → Prop} (h : ∀ o, Ψ o → Φ o)
    {s : S} {x : T} (hg : c.Generated Φ s x) : c.Generated Ψ s x := fun o ho => hg o (h o ho)

/-- **Generated relations compose** through a functional middle logic: the composite of the
relations `c` and `d` generate lies in the relation `c.comp d` generates. -/
theorem generated_comp (c : ObsComorphism A B) (d : ObsComorphism B C) (hB : B.Functional)
    {Φ : A.Obs → Prop} {s : S} {y : T} {x : U} (h₁ : c.Generated Φ s y)
    (h₂ : d.Generated (c.image Φ) y x) : (c.comp d).Generated Φ s x :=
  Silmaril.Proofs.Compiler.Explorer.generated_comp c d hB h₁ h₂

/-- For functional logics, a generated relation makes each observed value agree exactly. -/
theorem generated_iff (c : ObsComorphism A B) (hA : A.Functional) (hB : B.Functional)
    {Φ : A.Obs → Prop} {s : S} {x : T} (h : c.Generated Φ s x) {o : A.Obs} (ho : Φ o) (v : V) :
    A.Holds s o v ↔ B.Holds x (c.map o) v :=
  Silmaril.Proofs.Compiler.Explorer.generated_iff c hA hB h ho v

end ObsComorphism

namespace Mapping

variable {P : Problem σ τ R}

/-- Refinement is monotone in the generated relation. -/
theorem RefinesAt.mono {M : Mapping P} {G G' : Nat → τ → σ → τ → Prop} {K : Nat → Prop}
    (h : M.RefinesAt G K) (hG : ∀ k, K k → ∀ x0 s x, G k x0 s x → G' k x0 s x) :
    M.RefinesAt G' K := fun k hk x0 s x hr => hG k hk x0 s x (h k hk x0 s x hr)

/-- **What refinement of a comorphism relation gives**: at a point of `K`, every observable in
scope of related states has a value that holds of it in the source and of its translation in the
target. -/
theorem RefinesComorphism.observe {V : Type} {M : Mapping P} {A : ObsLogic σ V}
    {B : ObsLogic (τ × τ) V} {c : ObsComorphism A B} {scope : Nat → A.Obs → Prop}
    {K : Nat → Prop} (h : M.RefinesComorphism c scope K) {k : Nat} (hk : K k) {x0 : τ} {s : σ}
    {x : τ} (hr : M.rel k x0 s x) {o : A.Obs} (ho : scope k o) :
    ∃ v, A.Holds s o v ∧ B.Holds (x0, x) (c.map o) v := h k hk x0 s x hr o ho

/-- The mapping a comorphism generates refines the comorphism's relation at every point (the
specification of the construction). -/
theorem ofComorphism_refines {V : Type} {A : ObsLogic σ V} {B : ObsLogic (τ × τ) V}
    (srcAt : Nat → σ → Prop) (tgtAt : Nat → τ → Prop) (frame : Nat → τ → σ → τ → Prop)
    (c : ObsComorphism A B) (scope : Nat → A.Obs → Prop) :
    (ofComorphism (P := P) srcAt tgtAt frame c scope).RefinesComorphism c scope (fun _ => True) :=
  fun _ _ _ _ _ hr => hr.2

end Mapping

end Silmaril.Compiler.Explorer

end
