module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Defs

/-! Add a fresh unused slot to the front of the fixed quad loop's register bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening

open SeaOfNodes.Diamond (ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {fresh out : ValueSort Data}

/-- The reduct forgets the prepended capture. Old ports embed by `Port.tail`. -/
def project {T : Type u} {F : T → Type w} {head : T} {tail : List T} : Tuple F (head :: tail) → Tuple F tail
  | .cons _ rest => rest

def quad (fresh : ValueSort Data) (q : Quad Op regs) : Quad Op (fresh :: regs) :=
  ⟨q.ins, q.result, .tail q.dest, q.op, q.operands.map (fun _ p => .tail p)⟩

/-- Move every destination, use and terminator port under the fresh slot.
The preheader, header and both feedback blocks keep their instruction order. -/
def program (fresh : ValueSort Data) (p : Program Op regs out) : Program Op (fresh :: regs) out where
  preheader := p.preheader.map (quad fresh)
  header := p.header.map (quad fresh)
  again := .tail p.again
  select := .tail p.select
  result := .tail p.result
  feedback side := (p.feedback side).map (quad fresh)

/-- An unconstrained capture contributes no runtime coverage test. -/
def facts (fresh : ValueSort Data) {value : Data → Type w} (input : Tuple (Fact value) (dataPorts regs)) :
    Tuple (Fact value) (dataPorts (fresh :: regs)) :=
  .cons .overdefined input

/-- Retain the exact old coordinate comparisons underneath the new slot. -/
@[instance_reducible]
def extendEq {value : Data → Type w}
    (head : DecidableEq (sortValue value fresh)) (old : BankDecidableEq value (dataPorts regs)) :
    BankDecidableEq value (dataPorts (fresh :: regs)) :=
  ⟨fun i => Fin.cases (motive := fun j => DecidableEq (SeaOfNodes.Diamond.Val value (dataPorts (fresh :: regs))[j]))
    head old.atPort i⟩

/-- Preserve occurrence marks and the result fact, dropping only the fresh coordinate. -/
def projectState {value : Data → Type w} (state : SCCP.State value (fresh :: regs) out) :
    SCCP.State value regs out :=
  (state.1, fun i => state.2.1 i.succ, state.2.2)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening
