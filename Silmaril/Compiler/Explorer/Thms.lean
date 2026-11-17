module

public import Silmaril.Compiler.Explorer.Defs
import Silmaril.Proofs.Compiler.Explorer.Basic

/-!
# Compilation problems, mappings and generated relations: theorems

* `Problem.Refines.mono`: a stronger entry relation and a weaker result relation keep a
  refinement.
* `Problem.Refines.comp`: refinements compose vertically (source → intermediate → target).
* `SegmentDiscipline.all_of_listed`, `SegmentDiscipline.refines_of_listed`: valid listed edges and
  coverage give every edge, hence the refinement. Without coverage they give neither
  (`Det.Counterexample.edges_not_enough` in `Silmaril.Compiler.Explorer.Det.Thms`).
* `Gen.agrees_iff_reduct`: through the satisfaction condition of the semi-comorphism, agreement
  is agreement between the source reading and the *model translation* of the target reading.
* `Gen.agrees_comp`: generated relations compose along composed semi-comorphisms.
* `Gen.witnessed_of_reduct`: a witness in the model translation is a witness of the generated
  relation.
* `Mapping.RefinesAt.mono`, `Generator.mapping_refines` (the specification of the construction).

Proofs: `Silmaril.Proofs.Compiler.Explorer.Basic`.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.Inst

universe u₁ v₁ u₂ v₂ u₃ v₃ w m₁ m₂

variable {σ τ μ R T W : Type}

/-- **Monotonicity**: with the same semantics, a stronger entry relation and a weaker result
relation keep the refinement. -/
theorem Problem.Refines.mono {P Q : Problem σ τ R T} (hsrc : Q.src = P.src) (htgt : Q.tgt = P.tgt)
    (he : ∀ s x, Q.entry s x → P.entry s x) (hr : ∀ r v, P.result r v → Q.result r v)
    (h : P.Refines) : Q.Refines :=
  Silmaril.Proofs.Compiler.Explorer.refines_mono hsrc htgt he hr h

/-- **Vertical composition**: if `P` refines into an intermediate semantics and `Q` refines from
that same semantics, the composite refines. -/
theorem Problem.Refines.comp {P : Problem σ μ R W} {Q : Problem μ τ W T} (hmid : Q.src = P.tgt)
    (hP : P.Refines) (hQ : Q.Refines) : (P.comp Q).Refines :=
  Silmaril.Proofs.Compiler.Explorer.refines_comp hmid hP hQ

/-- **Valid listed edges and coverage give every edge.** -/
theorem SegmentDiscipline.all_of_listed {P : Problem σ τ R T} (D : SegmentDiscipline P)
    (N : D.Map) (L : List Nat) (he : ∀ k ∈ L, D.EdgeValid N k)
    (hc : (D.toMapping N).Covers L) : ∀ k, D.EdgeValid N k :=
  Silmaril.Proofs.Compiler.Explorer.all_of_listed D N L he hc

/-- **Valid listed edges, coverage, admissibility and the entry give the refinement.** -/
theorem SegmentDiscipline.refines_of_listed {P : Problem σ τ R T} (D : SegmentDiscipline P)
    (N : D.Map) (L : List Nat) (ha : D.Admissible N) (hs : (D.toMapping N).Starts)
    (he : ∀ k ∈ L, D.EdgeValid N k) (hc : (D.toMapping N).Covers L) : P.Refines :=
  D.sound N ha hs (D.all_of_listed N L he hc)

namespace Gen

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}}

/-- **Agreement is agreement with the model translation**, when the semi-comorphism's
satisfaction condition holds both ways on the observed sentences. -/
theorem agrees_iff_reduct (f : SemiComorphism A B) (hF : f.Fwd) (hB : f.Bwd) (S : A.Sign)
    (readS : σ → A.Mod S) (readT : τ → B.Mod (f.sig S)) (Ψ : A.Sen S → Prop)
    (hΨ : ∀ φ, Ψ φ → f.cls S φ) (s : σ) (x : τ) :
    Agrees f S readS readT Ψ s x ↔ ∀ φ, Ψ φ → (readS s ⊨[A] φ ↔ f.mod S (readT x) ⊨[A] φ) :=
  Silmaril.Proofs.Compiler.Explorer.agrees_iff_reduct f hF hB S readS readT Ψ hΨ s x

/-- **Generated relations compose** along the composite semi-comorphism `f ≫ˢ g`. -/
theorem agrees_comp (f : SemiComorphism A B) (g : SemiComorphism B C) (S : A.Sign)
    (readS : σ → A.Mod S) (readM : μ → B.Mod (f.sig S)) (readT : τ → C.Mod (g.sig (f.sig S)))
    (Ψ : A.Sen S → Prop) {s : σ} {y : μ} {x : τ}
    (h₁ : Agrees f S readS readM Ψ s y) (h₂ : Agrees g (f.sig S) readM readT (image f S Ψ) y x) :
    Agrees (f.comp g) S readS readT Ψ s x :=
  Silmaril.Proofs.Compiler.Explorer.agrees_comp f g S readS readM readT Ψ h₁ h₂

/-- **A witness in the model translation is a witness of the generated relation** (preservation
suffices). -/
theorem witnessed_of_reduct (f : SemiComorphism A B) (hF : f.Fwd) (S : A.Sign)
    (readS : σ → A.Mod S) (readT : τ → B.Mod (f.sig S)) {ι V : Type} (fam : ι → V → A.Sen S)
    (obs : ι → Prop) (hcls : ∀ i v, obs i → f.cls S (fam i v)) {s : σ} {x : τ}
    (h : ∀ i, obs i → ∃ v, readS s ⊨[A] fam i v ∧ f.mod S (readT x) ⊨[A] fam i v) :
    Witnessed f S readS readT fam obs s x :=
  Silmaril.Proofs.Compiler.Explorer.witnessed_of_reduct f hF S readS readT fam obs hcls h

end Gen

/-- Refinement is monotone in the generated relation. -/
theorem Mapping.RefinesAt.mono {P : Problem σ τ R T} {M : Mapping P} {G G' : Nat → σ → τ → Prop}
    {K : Nat → Prop} (h : M.RefinesAt G K) (hG : ∀ k, K k → ∀ s x, G k s x → G' k s x) :
    M.RefinesAt G' K := fun k hk s x hr => hG k hk s x (h k hk s x hr)

/-- The mapping a generator generates refines the generator's point relations (the
specification of the construction, not a correctness result). -/
theorem Generator.mapping_refines {A : Institution.{u₁, v₁, w, m₁, m₂}}
    {B : Institution.{u₂, v₂, w, m₁, m₂}} (g : Generator A B σ τ R T) {P : Problem σ τ R T}
    (srcAt : Nat → σ → Prop) (tgtAt : Nat → τ → Prop) (frame : Nat → σ → τ → Prop) :
    (g.mapping (P := P) srcAt tgtAt frame).RefinesAt g.pointRel (fun _ => True) :=
  fun _ _ _ _ hr => hr.2

end Silmaril.Compiler.Explorer

end
