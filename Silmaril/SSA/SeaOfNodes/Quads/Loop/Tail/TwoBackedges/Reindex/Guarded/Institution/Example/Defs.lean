module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

/-! Move the guarded selector past the byte, then move the byte past the loop test. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example

open CategoryTheory
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (bankEq facts regs word width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (admit)

abbrev initialSignature : Signature := { regs := regs, bankEq := bankEq }
abbrev middleSignature : Signature := { regs := [.predicate, word, .predicate] }
abbrev finalSignature : Signature := { regs := [word, .predicate, .predicate] }

def first : initialSignature ⟶ middleSignature :=
  Permutation.cons (Permutation.swap (T := SeaOfNodes.Diamond.Ty Width)
    (.value .predicate) (.value word) []) (.value .predicate)

def second : middleSignature ⟶ finalSignature :=
  Permutation.swap (T := SeaOfNodes.Diamond.Ty Width) (.value .predicate) (.value word) [.value .predicate]

def original : AdmittedAt initialSignature width :=
  (@admit regs width bankEq SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.program
    (facts (.constant ⟨true⟩))).toOption.get (by rfl)

def finalInput (side : Bool) : Valuation finalSignature :=
  .cons (7 : Word width) (.cons ⟨true⟩ (.cons ⟨side⟩ .nil))

def staged : Generated finalSignature width := ((Generated.lower original).map first).map second

def direct : Generated finalSignature width := (Generated.lower original).map (first ≫ second)

/-- Run the actual native, CF and numbered artifacts at their own budgets. -/
def run (p : Generated finalSignature width) (side : Bool) : Option Nat × Option Nat × Option Nat := by
  letI := finalSignature.bankEq
  let input := finalInput side
  let source := p.source.source
  let cfFuel := if side then 6 else 7
  exact ((source.source.runFrom model 5 0 input).map BitVec.toNat,
    (p.artifacts.cf.run evalOp cfFuel (encodeValues input)).map (fun env => (env.get .here).toNat),
    (p.artifacts.numbered.2.run (Join.model model) 1 input).map (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example
