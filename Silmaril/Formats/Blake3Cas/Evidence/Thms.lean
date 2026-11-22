module

public import Silmaril.Formats.Blake3Cas.Evidence.Defs
public import Silmaril.Crypto.Blake3.Range.EOF.Thms
import Silmaril.Proofs.Formats.Blake3Cas.Evidence

public section

namespace Silmaril.Formats.Blake3Cas

open Silmaril.Crypto.Blake3

theorem canonicalSpan (first size : Nat) : shapeSpan (geometry first size) = ⟨first, Bao.chunks size⟩ :=
  Proofs.Formats.Blake3Cas.canonicalSpan first size

theorem rootAnchor {size : Nat} {digest : Bytes} {cv : CV}
    (valid : validSize size) (exactBytes : digestBytes cv = digest) :
    Anchor size digest (geometry 0 size) true cv 0 true := Proofs.Formats.Blake3Cas.rootAnchor valid exactBytes

theorem Anchor.left {size base : Nat} {digest : Bytes} {left right : Shape}
    {root edge : Bool} {expected lcv rcv : CV}
    (parent : Anchor size digest (.fork left right) root expected base edge)
    (hit : parentCV root lcv rcv = expected) : Anchor size digest left false lcv base false :=
  Proofs.Formats.Blake3Cas.leftAnchor parent hit

theorem Anchor.right {size base : Nat} {digest : Bytes} {left right : Shape}
    {root edge : Bool} {expected lcv rcv : CV}
    (parent : Anchor size digest (.fork left right) root expected base edge)
    (hit : parentCV root lcv rcv = expected) : Anchor size digest right false rcv (base + left.size) edge :=
  Proofs.Formats.Blake3Cas.rightAnchor parent hit

theorem Anchor.openCell {size base : Nat} {digest bytes : Bytes} {shape : Shape}
    {root edge : Bool} {cv : CV} (anchor : Anchor size digest shape root cv base edge)
    (width : bytes.length = shape.size) (hit : subtreeCV? root shape bytes = some cv) :
    Checked concrete size digest base bytes ∧ (edge = true → CheckedEOF concrete size digest) :=
  Proofs.Formats.Blake3Cas.openedCell anchor width hit

end Silmaril.Formats.Blake3Cas
