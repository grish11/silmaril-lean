module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Defs

/-! # Finite closed certificates for guarded CFG pairs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open TwoRequest (Tag)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}

/-- The acyclic comparison's local query and exit clauses, with a relation
on the routed successors in place of recursive tree comparison. -/
def Head.MatchesWith (returns : Tag → Tag → Prop) (rel : Packet R → Packet T → Prop) :
    Head S R → Head S T → Prop
  | _, .exit _ true => True
  | .exit i false, .exit j false => returns i j
  | .diverge, .diverge => True
  | .request f arg next, .request g arg' next' => ∃ keys : f = g,
      arg.val = arg'.val ∧ ∀ reply : Packet (S.replies f),
        let target : Packet (S.replies g) := keys ▸ reply
        rel (next reply.1 reply.2) (next' target.1 target.2)
  | _, _ => False

/-- The ordinary unit-result comparison specializes terminal agreement to ordered tags. -/
def Head.Matches (rel : Packet R → Packet T → Prop) : Head S R → Head S T → Prop :=
  Head.MatchesWith Eq rel

def Head.checkPair [DecidableEq Φ] (replies : ReplyEnumeration S)
    (related : Packet R → Packet T → Bool) : Head S R → Head S T → Bool
  | _, .exit _ true => true
  | .exit i false, .exit j false => decide (i = j)
  | .diverge, .diverge => true
  | .request f arg next, .request g arg' next' =>
    if eq : (f, arg.val) = (g, arg'.val) then
      let keys : f = g := congrArg Prod.fst eq
      (replies.packets f).all fun reply =>
        let target : Packet (S.replies g) := keys ▸ reply
        related (next reply.1 reply.2) (next' target.1 target.2)
    else false
  | _, _ => false

/-- The raw packet key retains both the ordered label and constructor value. -/
def productContains (pairs : List (Packet R × Packet T)) (p : Packet R) (q : Packet T) : Bool :=
  pairs.any fun pair => decide (pair.1.raw = p.raw ∧ pair.2.raw = q.raw)

/-- Check the supplied relation at the entries and at every listed pair.
No graph traversal or decreasing rank is used. -/
def Table.checkProduct [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T)) : Bool :=
  productContains pairs ⟨g.entry, caller⟩ ⟨h.entry, caller'⟩ &&
    pairs.all fun (p, q) => (g.head caller p).checkPair replies (productContains pairs) (h.head caller' q)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
