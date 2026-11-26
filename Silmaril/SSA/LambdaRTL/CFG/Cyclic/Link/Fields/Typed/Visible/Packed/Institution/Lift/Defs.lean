module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PrimitiveSignature

open CategoryTheory
open Silmaril.Elgot.ITree.Finite (Event)

variable {F : Type} (signature : PrimitiveSignature F) {Target : Silmaril.Elgot.ITree.Signature.{0}}

/-- A source reply can be followed precisely when the target has a reply
that projects to it at the mapped complete request key. -/
def ReplyRealizable (f : signature.traceSignature.toSignature ⟶ Target) (key : signature.Request)
    (reply : signature.Reply key) : Prop :=
  ∃ r : (f.request ⟨_, Event.ask key⟩).1, f.reply ⟨_, Event.ask key⟩ r = reply

/-- Test membership in the image of each finite target reply map.
For arbitrary target reply types, callers may supply a certified mask instead. -/
def replyImageMask (f : signature.traceSignature.toSignature ⟶ Target)
    [∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    (key : signature.Request) (reply : signature.Reply key) : Bool :=
  decide (∃ r : (f.request ⟨_, Event.ask key⟩).1, f.reply ⟨_, Event.ask key⟩ r = reply)

/-- Filter intermediate replies at their exact mapped key before projecting
them back. A source reply is kept if any of its intermediate names survives.
With finite final replies and decidable intermediate reply equality,
test second-stage membership by enumerating the final reply preimages. -/
def projectReplyMask (f : signature.traceSignature.toSignature ⟶ Target)
    [finite : ∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.request ⟨_, Event.ask key⟩).1 → Bool)
    (key : signature.Request) (reply : signature.Reply key) : Bool :=
  decide (∃ r : (f.request ⟨_, Event.ask key⟩).1, admits key r = true ∧ f.reply ⟨_, Event.ask key⟩ r = reply)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PrimitiveSignature
