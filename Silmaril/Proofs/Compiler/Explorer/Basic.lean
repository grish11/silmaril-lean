module

public import Silmaril.Compiler.Explorer.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Thms

/-!
# Compilation problems, mappings and generated relations: proofs

The proofs behind `Silmaril.Compiler.Explorer.Thms`: monotonicity and vertical composition of
`Problem.Refines`, coverage for segment disciplines, and the relations semi-comorphisms generate
(through their satisfaction condition, and under composition).
-/

@[expose] public section

namespace Silmaril.Proofs.Compiler.Explorer

open Silmaril.Compiler.CompilesTo (Source)
open Silmaril.Compiler.Explorer
open Silmaril.Inst

universe u₁ v₁ u₂ v₂ u₃ v₃ w m₁ m₂

variable {σ τ μ R T W : Type}

theorem refines_mono {P Q : Problem σ τ R T} (hsrc : Q.src = P.src) (htgt : Q.tgt = P.tgt)
    (he : ∀ s x, Q.entry s x → P.entry s x) (hr : ∀ r v, P.result r v → Q.result r v)
    (h : P.Refines) : Q.Refines := by
  intro s x hq hsafe
  rw [hsrc] at hsafe
  obtain ⟨h1, h2, h3⟩ := h s x (he s x hq) hsafe
  rw [htgt, hsrc]
  refine ⟨h1, h2, fun y v hy hf => ?_⟩
  obtain ⟨t, r, ht, hfin, hres⟩ := h3 y v hy hf
  exact ⟨t, r, ht, hfin, hr r v hres⟩

theorem refines_comp {P : Problem σ μ R W} {Q : Problem μ τ W T} (hmid : Q.src = P.tgt)
    (hP : P.Refines) (hQ : Q.Refines) : (P.comp Q).Refines := by
  rintro s x ⟨m, hPe, hQe⟩ hsafe
  obtain ⟨hmSafe, -, hPres⟩ := hP s m hPe hsafe
  obtain ⟨hxSafe, hstuck, hQres⟩ := hQ m x hQe (hmid ▸ hmSafe)
  refine ⟨hxSafe, hstuck, fun y v hy hf => ?_⟩
  obtain ⟨t, w', ht, hfin, hres⟩ := hQres y v hy hf
  rw [hmid] at ht hfin
  obtain ⟨t', r, ht', hfin', hres'⟩ := hPres t w' ht hfin
  exact ⟨t', r, ht', hfin', w', hres', hres⟩

theorem all_of_listed {P : Problem σ τ R T} (D : SegmentDiscipline P) (N : D.Map) (L : List Nat)
    (he : ∀ k ∈ L, D.EdgeValid N k) (hc : (D.toMapping N).Covers L) : ∀ k, D.EdgeValid N k := by
  intro k
  by_cases hk : k ∈ L
  · exact he k hk
  · exact D.vacuous N k (hc k hk)

section Gen

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}}

theorem agrees_iff_reduct (f : SemiComorphism A B) (hF : f.Fwd) (hB : f.Bwd) (S : A.Sign)
    (readS : σ → A.Mod S) (readT : τ → B.Mod (f.sig S)) (Ψ : A.Sen S → Prop)
    (hΨ : ∀ φ, Ψ φ → f.cls S φ) (s : σ) (x : τ) :
    Gen.Agrees f S readS readT Ψ s x ↔
      ∀ φ, Ψ φ → (readS s ⊨[A] φ ↔ f.mod S (readT x) ⊨[A] φ) := by
  have key : ∀ φ, Ψ φ → (readT x ⊨[B] f.sen S φ ↔ f.mod S (readT x) ⊨[A] φ) := fun φ hφ =>
    ⟨f.sat_bwd hB S (readT x) φ (hΨ φ hφ), f.sat_fwd hF S (readT x) φ (hΨ φ hφ)⟩
  constructor
  · intro h φ hφ; exact (h φ hφ).trans (key φ hφ)
  · intro h φ hφ; exact (h φ hφ).trans (key φ hφ).symm

theorem agrees_comp (f : SemiComorphism A B) (g : SemiComorphism B C) (S : A.Sign)
    (readS : σ → A.Mod S) (readM : μ → B.Mod (f.sig S)) (readT : τ → C.Mod (g.sig (f.sig S)))
    (Ψ : A.Sen S → Prop) {s : σ} {y : μ} {x : τ}
    (h₁ : Gen.Agrees f S readS readM Ψ s y)
    (h₂ : Gen.Agrees g (f.sig S) readM readT (Gen.image f S Ψ) y x) :
    Gen.Agrees (f.comp g) S readS readT Ψ s x :=
  fun φ hφ => (h₁ φ hφ).trans (h₂ (f.sen S φ) ⟨φ, hφ, rfl⟩)

theorem witnessed_of_reduct (f : SemiComorphism A B) (hF : f.Fwd) (S : A.Sign)
    (readS : σ → A.Mod S) (readT : τ → B.Mod (f.sig S)) {ι V : Type} (fam : ι → V → A.Sen S)
    (obs : ι → Prop) (hcls : ∀ i v, obs i → f.cls S (fam i v)) {s : σ} {x : τ}
    (h : ∀ i, obs i → ∃ v, readS s ⊨[A] fam i v ∧ f.mod S (readT x) ⊨[A] fam i v) :
    Gen.Witnessed f S readS readT fam obs s x := by
  intro i hi
  obtain ⟨v, hs, hx⟩ := h i hi
  exact ⟨v, hs, f.sat_fwd hF S (readT x) (fam i v) (hcls i v hi) hx⟩

end Gen

end Silmaril.Proofs.Compiler.Explorer

end
