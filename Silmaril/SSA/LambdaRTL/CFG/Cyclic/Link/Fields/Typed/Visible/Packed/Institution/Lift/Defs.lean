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

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PrimitiveSignature
