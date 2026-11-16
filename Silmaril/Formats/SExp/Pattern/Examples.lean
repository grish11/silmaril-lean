module

public import Silmaril.Formats.SExp.Pattern.Thms

/-!
# AST encodings: why argument vectors need a fixed length

One variadic tag whose payload is a list of S-expressions, encoded as themselves: the node with
one argument `(())` and no children and the node with no arguments and one child `t()` both
encode as `(() (()))`. `AST.encode_injective` excludes this with `ArgLenFixed`.
-/

@[expose] public section

namespace Silmaril.Formats.Examples

/-- One variadic tag with a list of S-expressions as payload. -/
def listSig : AstSig := ⟨Unit, fun _ => List (SExp Unit), fun _ => .star⟩

def enc : AST listSig → SExp Unit := AST.encode (fun _ => .atom ()) (fun _ a => a)

def leafNode : AST listSig := AST.node (S := listSig) () [] []

def argNode : AST listSig := AST.node (S := listSig) () [SExp.ofList [.atom ()]] []

def childNode : AST listSig := AST.node (S := listSig) () [] [leafNode]

theorem enc_collides : enc argNode = enc childNode ∧ argNode ≠ childNode := by
  refine ⟨rfl, ?_⟩
  intro h
  simp [argNode, childNode, AST.node, TExpr.ofList] at h

end Silmaril.Formats.Examples
