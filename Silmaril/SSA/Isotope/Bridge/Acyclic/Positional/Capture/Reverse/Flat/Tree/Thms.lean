module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.WeakTree

/-! # Weak-tree semantics of the actual witnessed flat table -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction
open Morphism.CaseSSA (erase)

universe u v w x

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {n exits : Nat} {β : BoundCtx τ n} {L : LCtx τ} {Events : Type w → Type w} {α : Type x}

/-- The reconstructed table runs the original grammar at the same ordered
exits, using the ordinary flat region's weak-tree interpreter. -/
theorem ResultGrammar.flat_tree {source : Operand Φ β (Region.packedExitType L)}
    (g : ResultGrammar source) (length : L.length = exits) (raw : Primitive Events Φ α) (env : Env α) :
    term raw env (erase source.1) =
      (region raw env (g.toTable.toFlat length).erase >>= fun p => pure (Region.packedExitValue p.1 p.2)) := by
  rw [g.toTable.toFlat_erase]
  exact (congrArg (fun a => term raw env (erase a.1)) g.toTable_toLetCase).symm.trans
    (Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.toLetCase_tree raw g.toTable env)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
