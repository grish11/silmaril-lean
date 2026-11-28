module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Coverage
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Packed
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Separation

/-! # Native normalization and reflection for structural signatures -/

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace
open scoped Structural

variable {α Φ : Type} [Signature α Φ]

/-- Normalize an exact native derivation after supplying assemblies for the
source variables. Effects in arguments and products retain their native order. -/
theorem normalize_exact {n m : Nat} {source : Context α n} {target : Context α m}
    {t : Term Φ n} {A : Ty α} (d : Derivation Φ Γ₀ source t A) (σ : AssemblyEnv source target) :
    Normalizes target (t.bsubst σ.terms) A :=
  normalize_exact_proof d σ

/-- A packed structural input supplies its own assembly, including the empty
and singleton cases of an ordered finite input list. -/
theorem normalize_packed {s : Shape α} {t : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) :
    ∃ u : Term Φ (packedUnpack s).size, ∃ _ : Normal (packedUnpack s).context u A,
      Equiv false Γ₀ (Packed s) t ((packedUnpack s).split.wrap u) A :=
  normalize_packed_proof d

/-- One concrete separating input suffices. Replies allocate fresh atom
tokens by structural position, and generator events retain unit replies. -/
theorem packed_run_eq_iff_native {s : Shape α} {t u : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (e : Derivation Φ Γ₀ (Packed s) u A) :
    run d (packedEnv s (s.fresh 0)) = run e (packedEnv s (s.fresh 0)) ↔
      Equiv false Γ₀ (Packed s) t u A := by
  classical
  exact packed_reflect_proof d e

/-- Unfold exactly one typed request in the trace model. -/
theorem mem_request_trace {A : Type} {f : Φ} {a : Value (Signature.argument (α := α) f).ty}
    {k : Value (Signature.reply (α := α) f).ty → Trace α Φ A} {z : A} {w : Log α Φ} :
    (z, w) ∈ (((model (α := α)).eval f a) >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, a, reply⟩ * tail = w :=
  mem_request

end Silmaril.Isotope.LetSeq.StraightLine.Structural
