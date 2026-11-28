module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

/-! # Untyped value erasure for positional LambdaSSA in an Elgot monad -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Erasure

open Silmaril.Elgot
open Interaction (Transfer BlockInput splitTransfer)

universe u v w

abbrev Primitive (m : Type u → Type w) (Φ : Type v) (α : Type u) :=
  Φ → Value α → m (Value α)

variable {m : Type u → Type w} [Monad m] {Φ : Type v} {α : Type u}

/-- Erase intermediate typing choices. The supplied fallback is used only
when the erased value has a shape excluded by exact typing. -/
def term (bad : m (Value α)) (instr : Primitive m Φ α) (env : Env α) :
    Tm Φ → m (Value α)
  | .var i => pure (env i)
  | .op op a => term bad instr env a >>= instr op
  | .let₁ a b => term bad instr env a >>= fun v => term bad instr (extend env v) b
  | .pair a b => term bad instr env a >>= fun x => term bad instr env b >>= fun y => pure (.pair x y)
  | .unit => pure .unit
  | .let₂ a b => term bad instr env a >>= fun
    | .pair x y => term bad instr (extend (extend env x) y) b
    | _ => bad
  | .inl a => term bad instr env a >>= fun v => pure (.inl v)
  | .inr a => term bad instr env a >>= fun v => pure (.inr v)
  | .case a l r => term bad instr env a >>= fun
    | .inl v => term bad instr (extend env v) l
    | .inr v => term bad instr (extend env v) r
    | _ => bad
  | .abort a => term bad instr env a >>= fun _ => bad

variable [Iterate m]

/-- The erased dispatcher uses the original label arity and value packet.
Its state does not contain the independently inferred local label types. -/
noncomputable def region (badTerm : m (Value α)) (badRegion : m (Transfer α))
    (instr : Primitive m Φ α) (env : Env α) : Region Φ → m (Transfer α)
  | .br i a => term badTerm instr env a >>= fun v => pure (i, v)
  | .let₁ a b => term badTerm instr env a >>= fun v => region badTerm badRegion instr (extend env v) b
  | .let₂ a b => term badTerm instr env a >>= fun
    | .pair x y => region badTerm badRegion instr (extend (extend env x) y) b
    | _ => badRegion
  | .case a l r => term badTerm instr env a >>= fun
    | .inl v => region badTerm badRegion instr (extend env v) l
    | .inr v => region badTerm badRegion instr (extend env v) r
    | _ => badRegion
  | .cfg e arity blocks =>
    let step := fun p : BlockInput α arity =>
      region badTerm badRegion instr (extend env p.2) (blocks p.1) >>= fun out => pure (splitTransfer arity out)
    region badTerm badRegion instr env e >>= fun out => Sum.elim pure (iter step) (splitTransfer arity out)

end Silmaril.Isotope.LambdaSSA.Semantics.Erasure
