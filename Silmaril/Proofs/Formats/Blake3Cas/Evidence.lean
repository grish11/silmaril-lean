module

public import Silmaril.Formats.Blake3Cas.Evidence.Defs
public import Silmaril.Crypto.Blake3.Range.EOF.Thms

public section

namespace Silmaril.Proofs.Formats.Blake3Cas

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas

private theorem splitBounds (size : Nat) (large : 1024 < size) :
    0 < splitBytes size ∧ splitBytes size < size := by
  have positive : 0 < (size - 1) / 1024 := by omega
  have below := (Nat.le_log2 (Nat.ne_of_gt positive)).mp (Nat.le_refl ((size - 1) / 1024).log2)
  have nonzero := Nat.two_pow_pos ((size - 1) / 1024).log2
  unfold splitBytes
  omega

theorem canonicalSpan (first size : Nat) : shapeSpan (geometry first size) = ⟨first, Bao.chunks size⟩ := by
  rw [geometry]
  split
  · have single : Bao.chunks size = 1 := by unfold Bao.chunks Bao.chunkBytes; omega
    simp [shapeSpan, single]
  · have bounds := splitBounds size (by omega)
    have countSplit : Bao.chunks (splitBytes size) + Bao.chunks (size - splitBytes size) = Bao.chunks size := by
      unfold Bao.chunks Bao.chunkBytes splitBytes at *
      omega
    simp only [shapeSpan, canonicalSpan first (splitBytes size),
      canonicalSpan (first + splitBytes size / 1024) (size - splitBytes size), countSplit]
termination_by size
decreasing_by all_goals have := splitBounds size (by omega); omega

theorem rootAnchor {size : Nat} {digest : Bytes} {cv : CV}
    (valid : validSize size) (exactBytes : digestBytes cv = digest) :
    Anchor size digest (geometry 0 size) true cv 0 true := by
  constructor
  intro opening trace
  exact ⟨opening, ⟨valid, cv, trace, exactBytes⟩, fun read => by simpa using read,
    fun _ edge => edge⟩

theorem leftAnchor {size base : Nat} {digest : Bytes} {left right : Shape}
    {root edge : Bool} {expected lcv rcv : CV}
    (parent : Anchor size digest (.fork left right) root expected base edge)
    (hit : parentCV root lcv rcv = expected) : Anchor size digest left false lcv base false := by
  constructor
  intro opening trace
  have joined : Trace concrete root (.fork left right) (.fork opening (.opaque rcv)) expected :=
    .fork trace (.opaque right rcv) (congrArg some hit)
  obtain ⟨full, checked, read, _⟩ := parent.lift joined
  exact ⟨full, checked, fun part => read (.left part), by simp⟩

theorem rightAnchor {size base : Nat} {digest : Bytes} {left right : Shape}
    {root edge : Bool} {expected lcv rcv : CV}
    (parent : Anchor size digest (.fork left right) root expected base edge)
    (hit : parentCV root lcv rcv = expected) :
    Anchor size digest right false rcv (base + left.size) edge := by
  constructor
  intro opening trace
  have joined : Trace concrete root (.fork left right) (.fork (.opaque lcv) opening) expected :=
    .fork (.opaque left lcv) trace (congrArg some hit)
  obtain ⟨full, checked, read, rightmost⟩ := parent.lift joined
  exact ⟨full, checked, fun part => by simpa only [Nat.add_assoc] using read (.right part), rightmost⟩

theorem readWhole (shape : Shape) (bytes : Bytes) (width : bytes.length = shape.size) :
    Read shape (disclose shape bytes) 0 bytes := by
  induction shape generalizing bytes with
  | leaf => exact .leaf width
  | fork left right leftIH rightIH =>
    have takeSize : (bytes.take left.size).length = left.size := by
      simp [Shape.size] at width
      simp [width]
    have dropSize : (bytes.drop left.size).length = right.size := by
      simp [Shape.size] at width
      simp [width]
    have joined := Read.join (leftIH _ takeSize) (rightIH _ dropSize) (by simp [takeSize])
    simpa only [List.take_append_drop, disclose] using joined

theorem openedCell {size base : Nat} {digest bytes : Bytes} {shape : Shape}
    {root edge : Bool} {cv : CV} (anchor : Anchor size digest shape root cv base edge)
    (width : bytes.length = shape.size) (hit : subtreeCV? root shape bytes = some cv) :
    Checked concrete size digest base bytes ∧ (edge = true → CheckedEOF concrete size digest) := by
  obtain ⟨full, checked, read, rightmost⟩ := anchor.lift (eval_graph.mp hit)
  exact ⟨⟨full, checked, by simpa using read (readWhole shape bytes width)⟩,
    fun edge => ⟨full, checked, rightmost edge (disclose_exposesEOF shape bytes)⟩⟩

end Silmaril.Proofs.Formats.Blake3Cas
