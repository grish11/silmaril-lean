module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.PureAssembly
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Reflection
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Separation

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Isotope.Semantics (BoundEnv)

set_option backward.isDefEq.respectTransparency false

theorem product_normalize_proof {n : Nat} {β : BoundCtx Types n} {A : Types} {t : Term n}
    (p : ProductProgram β t A) :
    ∃ u : Term n, ∃ _ : ProductCanonical β u A, Equiv false Γ₀ β t u A := by
  induction p with
  | ret v =>
    obtain ⟨w, replay⟩ := assembly_normalize_proof v
    exact ⟨_, .result w, replay⟩
  | request f arg rest ih =>
    obtain ⟨v, ha⟩ := assembly_normalize_proof arg
    obtain ⟨_, w, hb⟩ := ih
    exact ⟨_, .step f v w, .let₂ (.op ha) hb⟩
  | bound f arg rest ih =>
    obtain ⟨v, ha⟩ := assembly_normalize_proof arg
    obtain ⟨_, w, hb⟩ := ih
    have expand := Equiv.bindPair (pureEff := false) (LocallyNameless.HasType.op (f := f) ha.hasType.1) hb.hasType.1
    exact ⟨_, .step f v w, expand.symm.trans (.let₂ (.op ha) hb)⟩

theorem product_run_iff_native_proof {n : Nat} {β : BoundCtx Types n} {A : Types} {t u : Term n}
    (p : ProductProgram β t A) (q : ProductProgram β u A)
    (d : Derivation Request Γ₀ β t A) (e : Derivation Request Γ₀ β u A)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    run d ρ = run e ρ ↔ Equiv false Γ₀ β t u A := by
  refine ⟨fun h => ?_, fun h => seq_sound_proof d e h ρ⟩
  obtain ⟨t', p', hp⟩ := product_normalize_proof p
  obtain ⟨u', q', hq⟩ := product_normalize_proof q
  have runs := (seq_sound_proof d p'.derivation hp ρ).symm.trans
    (h.trans (seq_sound_proof e q'.derivation hq ρ))
  have same : t' = u' := product_canonical_eq_proof p' q' ρ fresh sep runs
  rw [same] at hp
  exact hp.trans hq.symm

theorem product_embed_iff_native_proof {n : Nat} {β : BoundCtx Types n} {A : Types} {t u : Term n}
    (p : ProductProgram β t A) (q : ProductProgram β u A)
    (d : Derivation Request Γ₀ β t A) (e : Derivation Request Γ₀ β u A)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    LetCase.LocallyNameless.Equiv false Γ₀ β (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) A ↔
      Equiv false Γ₀ β t u A := by
  refine ⟨fun h => (product_run_iff_native_proof p q d e ρ fresh sep).mp ?_, Morphism.SeqCase.embed_equiv⟩
  simpa only [run, Morphism.SeqCase.denote_derivation] using
    case_sound_proof (Morphism.SeqCase.derivation d) (Morphism.SeqCase.derivation e) h ρ

theorem entry_product_run_iff_native_proof {t u : Term 3} {A : Types}
    (p : ProductProgram ((input.snoc Atom).snoc Atom) t A)
    (q : ProductProgram ((input.snoc Atom).snoc Atom) u A)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t A)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u A) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) A := by
  refine ⟨fun h => ?_, fun h => seq_sound_proof (entry d) (entry e) h _⟩
  rw [entry_run_proof, entry_run_proof] at h
  have body := (product_run_iff_native_proof p q d e _ 2
    (separating_snoc_proof (separating_snoc_proof input_separating))).mp h
  exact .let₂ (.refl .bv) body

theorem entry_product_embed_iff_native_proof {t u : Term 3} {A : Types}
    (p : ProductProgram ((input.snoc Atom).snoc Atom) t A)
    (q : ProductProgram ((input.snoc Atom).snoc Atom) u A)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t A)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u A) :
    LetCase.LocallyNameless.Equiv false Γ₀ input
      (Morphism.SeqCase.embed (.let₂ (.bv 0) t)) (Morphism.SeqCase.embed (.let₂ (.bv 0) u)) A ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) A := by
  refine ⟨fun h => (entry_product_run_iff_native_proof p q d e).mp ?_, Morphism.SeqCase.embed_equiv⟩
  simpa only [run, Morphism.SeqCase.denote_derivation] using
    case_sound_proof (Morphism.SeqCase.derivation (entry d))
      (Morphism.SeqCase.derivation (entry e)) h (packetEnv (0, 1))

end Silmaril.Isotope.LetSeq.StraightLine
