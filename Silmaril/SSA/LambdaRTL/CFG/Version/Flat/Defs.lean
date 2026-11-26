module

public import Silmaril.SSA.LambdaRTL.CFG.Defs

/-! # Reifying the readback of a forward CFG

Readback keeps the original labels and cases inline. Its inverse recognizes
a chain of outer joins over a block body, with a block body as every handler.
In particular, cases within a terminator can contain only terminators.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v}

/-- Recognize a branch or a tree of conditional terminators. -/
def Term.ofRegion? : Region V K F → Option (Term V K F)
  | .br label arg => some (.br label arg)
  | .case op x left y right =>
      (ofRegion? left).bind fun leftTerm =>
        (ofRegion? right).map fun rightTerm => .case op x leftTerm y rightTerm
  | _ => none

/-- Recognize an instruction prefix followed by a terminator. -/
def Body.ofRegion? : Region V K F → Option (Body V K F)
  | .let1 x op body => (ofRegion? body).map (.let1 x op)
  | .let2 x y op body => (ofRegion? body).map (.let2 x y op)
  | region => (Term.ofRegion? region).map .term

/-- Reify a region in the image of `CFG.toRegion`. Peeling the outermost join
first finds the last block, so consing each handler restores the forward order. -/
def ofRegion? (region : Region V K F) : Option (CFG V K F) :=
  collect region []
where
  collect : Region V K F → List (K × Block V K F) → Option (CFG V K F)
    | .join entry label param handler, blocks =>
        (Body.ofRegion? handler).bind fun body =>
          collect entry ((label, ⟨param, body⟩) :: blocks)
    | region@(.br ..), blocks
    | region@(.let1 ..), blocks
    | region@(.let2 ..), blocks
    | region@(.case ..), blocks => (Body.ofRegion? region).map fun entry => ⟨entry, blocks⟩

end Silmaril.SSA.LambdaRTL.CFG
