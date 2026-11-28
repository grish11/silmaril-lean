module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Separation

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)

set_option backward.isDefEq.respectTransparency false

theorem run_eq_iff_normal_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    run d ρ = run e ρ ↔ p.normal = q.normal := by
  have left := seq_sound_proof d (canonicalDerivation (normalWitness p)) (replay_proof p) ρ
  have right := seq_sound_proof e (canonicalDerivation (normalWitness q)) (replay_proof q) ρ
  rw [left, right]
  refine ⟨canonical_eq_proof (normalWitness p) (normalWitness q) ρ fresh sep, fun same => ?_⟩
  have identical : Equiv false Γ₀ β p.normal q.normal Atom := by
    rw [← same]
    exact .refl (canonicalDerivation (normalWitness p)).toHasType
  exact seq_sound_proof _ _ identical ρ

theorem native_iff_normal_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    Equiv false Γ₀ β t u Atom ↔ p.normal = q.normal := by
  constructor
  · intro h
    exact (run_eq_iff_normal_proof p q d e ρ fresh sep).mp (seq_sound_proof d e h ρ)
  · intro h
    have left := replay_proof p
    rw [h] at left
    exact left.trans (replay_proof q).symm

theorem embed_iff_native_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    LetCase.LocallyNameless.Equiv false Γ₀ β (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) Atom ↔
      Equiv false Γ₀ β t u Atom := by
  refine ⟨fun caseEq => ?_, Morphism.SeqCase.embed_equiv⟩
  have equal := case_sound_proof (Morphism.SeqCase.derivation d) (Morphism.SeqCase.derivation e) caseEq ρ
  have runs : run d ρ = run e ρ := by
    simpa only [Morphism.SeqCase.denote_derivation, run] using equal
  exact (native_iff_normal_proof p q d e ρ fresh sep).mpr
    ((run_eq_iff_normal_proof p q d e ρ fresh sep).mp runs)

theorem entry_run_proof {body : Term 3} {A : Types}
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) body A) (x y : Nat) :
    run (entry d) (packetEnv (x, y)) =
      run d (((packetEnv (x, y)).snoc (A := Atom) x).snoc (A := Atom) y) := by
  simp only [run, entry, Derivation.denote, pure_bind]
  rfl

private theorem packet_no_atom (x : Slot input) : False := by
  have index : x.1 = 0 := Fin.eq_zero _
  have sort := x.2
  rw [index] at sort
  cases sort

theorem input_separating : Separating (packetEnv (0, 1)) 0 :=
  ⟨fun x _ _ => (packet_no_atom x).elim, fun x => (packet_no_atom x).elim⟩

theorem entry_iff_normal_proof {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔ p.normal = q.normal := by
  rw [entry_run_proof, entry_run_proof]
  exact run_eq_iff_normal_proof p q d e _ 2 (separating_snoc_proof (separating_snoc_proof input_separating))

theorem entry_iff_native_proof {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom := by
  refine ⟨fun equal => ?_, fun h => seq_sound_proof (entry d) (entry e) h _⟩
  have normal := (entry_iff_normal_proof p q d e).mp equal
  have left := replay_proof p
  rw [normal] at left
  exact .let₂ (.refl .bv) (left.trans (replay_proof q).symm)

theorem entry_embed_iff_native_proof {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    LetCase.LocallyNameless.Equiv false Γ₀ input
      (Morphism.SeqCase.embed (.let₂ (.bv 0) t)) (Morphism.SeqCase.embed (.let₂ (.bv 0) u)) Atom ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom := by
  refine ⟨fun h => (entry_iff_native_proof p q d e).mp ?_, Morphism.SeqCase.embed_equiv⟩
  simpa only [run, Morphism.SeqCase.denote_derivation] using
    case_sound_proof (Morphism.SeqCase.derivation (entry d))
      (Morphism.SeqCase.derivation (entry e)) h (packetEnv (0, 1))

end Silmaril.Isotope.LetSeq.StraightLine
