module

public import Silmaril.SSA.Isotope.BrookesLetParIter.Defs
public import Silmaril.SSA.Isotope.LetParIter.Thms
import Silmaril.Proofs.SSA.Isotope.BrookesLetParIter.Interpretation

/-! # LetParIter soundness for finite completed SC observations -/

public section

namespace Silmaril.Isotope.BrookesLetParIter

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Semantics.Brookes

/-- Every generated LetParIter equation preserves its finite completed SC denotation. -/
theorem sound {ν : Type} [DecidableEq ν] {Γ : Ctx ν SCType} {n : Nat}
    {β : BoundCtx SCType n} {a b : LetParIter.Tm ν Instr n} {A : SCType}
    {da : Parallel.Derivation Instr Γ β a A} {db : Parallel.Derivation Instr Γ β b A}
    (h : LetParIter.Equiv (⊥ : Bool) Γ da db) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetParIter.denote (ε := Bool) pairing da γ ρ = LetParIter.denote (ε := Bool) pairing db γ ρ :=
  LetParIter.sound pairing h γ ρ

/-- The common tier interpreter preserves the same equations on this SC signature. -/
theorem interpret_sound {ν : Type} [DecidableEq ν] {Γ : Ctx ν SCType} {n : Nat}
    {β : BoundCtx SCType n} {a b : LetParIter.Tm ν Instr n} {A : SCType}
    {da : Parallel.Derivation Instr Γ β a A} {db : Parallel.Derivation Instr Γ β b A}
    (h : LetParIter.Equiv (⊥ : Bool) Γ da db) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetParIter.interpret (ε := Bool) pairing da γ ρ =
      LetParIter.interpret (ε := Bool) pairing db γ ρ :=
  LetParIter.interpret_sound pairing h γ ρ

/-- Identity is the sole bottom-effect instruction. -/
theorem pure_instruction_iff (op : Instr) :
    (instrEff op : Bool) = ⊥ ↔ op = .identity :=
  Proofs.SSA.Isotope.BrookesLetParIter.pure_instruction_iff op

/-- An abort continuation from the empty type contributes no completed trace. -/
theorem abort_empty {A : Type} (p : M Empty) :
    p.bind (fun e : Empty => e.elim) = (⊥ : M A) :=
  Proofs.SSA.Isotope.BrookesLetParIter.abort_empty p

/-- A free mutex can be acquired without interference. -/
theorem acquire_free (thread : Bool) (n : Nat) :
    (eval (.acquire thread) ()).completes (state n none) (state n (some thread)) () :=
  Proofs.SSA.Isotope.BrookesLetParIter.acquire_free thread n

/-- An acquire starting with an occupied mutex cannot complete without interference. -/
theorem acquire_held (thread owner : Bool) (n : Nat) (t : Store) :
    ¬(eval (.acquire thread) ()).completes (state n (some owner)) t () :=
  Proofs.SSA.Isotope.BrookesLetParIter.acquire_held thread owner n t

/-- The current owner can release the mutex without interference. -/
theorem release_owner (thread : Bool) (n : Nat) :
    (eval (.release thread) ()).completes (state n (some thread)) (state n none) () :=
  Proofs.SSA.Isotope.BrookesLetParIter.release_owner thread n

/-- A nonowner cannot complete a release without interference. -/
theorem release_nonowner (thread owner : Bool) (hne : owner ≠ thread) (n : Nat) (t : Store) :
    ¬(eval (.release thread) ()).completes (state n (some owner)) t () :=
  Proofs.SSA.Isotope.BrookesLetParIter.release_nonowner thread owner hne n t

end Silmaril.Isotope.BrookesLetParIter
