module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs

/-! # Read selected final registers into the external branch payload -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- The same right-nested, unit-terminated tuple as the versioner's packet. -/
def reads : List V → Val V
  | [] => .unit
  | x :: xs => .pair (.var x) (reads xs)

/-- Retain the original payload and the specified fields of the exit store. -/
def project (model : Model F M α) (fields : K → List V) (out : Transfer V K α) :
    Transfer V K α :=
  (out.1, model.pair out.2.1 (Version.packVal model out.2.2 (fields out.1)), out.2.2)

def attachTerm (isExit : K → Bool) (fields : K → List V) : Term V K F → Term V K F
  | .br k value => .br k (if isExit k then .pair value (reads (fields k)) else value)
  | .case op x left y right =>
      .case op x (attachTerm isExit fields left) y (attachTerm isExit fields right)

def attachBody (isExit : K → Bool) (fields : K → List V) : Body V K F → Body V K F
  | .term tail => .term (attachTerm isExit fields tail)
  | .let1 x op body => .let1 x op (attachBody isExit fields body)
  | .let2 x y op body => .let2 x y op (attachBody isExit fields body)

/-- Extend each branch to a missing label. Internal branch arguments, block
order, binders and primitive operands are reused as written. -/
def attach [DecidableEq K] (fields : K → List V) (graph : CFG V K F) : CFG V K F :=
  let isExit := fun label => (graph.blocks.lookup label).isNone
  ⟨attachBody isExit fields graph.entry,
    graph.blocks.map fun item =>
      (item.1, ⟨item.2.param, attachBody isExit fields item.2.body⟩)⟩

/-- Only a pending transfer to a missing label already carries its projected
payload. The original argument and store travel unchanged on internal edges. -/
def encode [DecidableEq K] (model : Model F M α) (fields : K → List V)
    (graph : CFG V K F) (out : Transfer V K α) : Transfer V K α :=
  if (graph.blocks.lookup out.1).isNone then project model fields out else out

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut
