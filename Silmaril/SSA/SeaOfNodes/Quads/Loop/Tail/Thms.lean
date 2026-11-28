module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Correctness

/-! # Checked source edges, typed Φ columns and exact tail-loop observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail

open Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Wires)
open Join (Block)
open Blocks (Bank)
open SeaOfNodes.Loop (Incoming)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

theorem Source.runFrom_mono {n : Nat} {source : Source Op regs out n} (m : Model.{u, v, w} Op)
    {fuel larger : Nat} {id : Fin n} {bank : Bank (regs := regs) m} {value : sortValue m.value out}
    (enough : fuel ≤ larger) (returned : source.runFrom m fuel id bank = some value) :
    source.runFrom m larger id bank = some value :=
  Proofs.runFrom_mono m enough returned

variable {src : Source Op regs out} {p : Program Op regs out}

theorem Source.check_source (p : Program Op regs out) : p.source.check = some p := rfl

/-- The checker preserves every original block and terminator on success. -/
theorem Source.check_sound (accepted : src.check = some p) : p.source = src :=
  Proofs.source_of_check accepted

/-- Entry reaches the header with the preheader's own outgoing column. -/
theorem Program.entry_column (p : Program Op regs out) :
    p.lower.phiInputs .entry = p.fuse.entryTransfer.outgoing := rfl

/-- Feedback reaches the header with the latch's outgoing versions, computed
in the context of the preceding header's producers. -/
theorem Program.feedback_column (p : Program Op regs out) :
    p.lower.phiInputs .backedge = p.feedbackColumn :=
  Proofs.feedback_column p

/-- Cutting an ordered block at an unconditional edge gives the same outgoing
wires, with the same producer numbering, as compiling the concatenation. -/
theorem compile_append_outgoing {args : List (Ty Data)} {past : List (List (Ty Data))}
    (first second : Block Op regs) (current : Wires args past (dataPorts regs)) :
    HEq (CFG.compileBlock (first ++ second) current).outgoing
      (CFG.compileBlock second (CFG.compileBlock first current).outgoing).outgoing :=
  Proofs.append_outgoing first second current

variable (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)

/-- Each incoming occurrence latches the complete predecessor bank simultaneously. -/
theorem Program.latch_agrees (p : Program Op regs out) (old : Bank (regs := regs) m)
    (edge : Incoming) :
    p.fuse.latch m edge input old =
      edge.select (p.entry.eval m input) (p.latch.body.eval m (p.header.eval m old)) :=
  Proofs.latch_agrees p m input old edge

/-- One preheader visit and one header/latch pair are needed before the first
return. Each additional native backedge costs another pair of source visits. -/
theorem Source.lower_run (accepted : src.check = some p) (fuel : Nat) :
    src.run m fuel input =
      if 3 ≤ fuel then p.lower.evalBackedges m ((fuel - 3) / 2) input else none := by
  rw [← Source.check_sound accepted]
  exact Proofs.lower_run p m input fuel

/-- Finite native evaluation and the bounded source runner agree on all
returned values in both directions. -/
theorem Source.returns_iff (accepted : src.check = some p) (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ ∃ fuel, src.run m fuel input = some result :=
  Proofs.returns_iff p m input accepted result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail
