module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! Read the compiled abstract block as its ordered typed register writes. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Proofs

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact evalFacts)
open RVSDG (Locals Tuple Wires)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} (m : Model.{u, v, w} Op)

private theorem compile_eval (block : Block Op regs)
    {args : List (SeaOfNodes.Diamond.Ty Data)} {past : List (List (SeaOfNodes.Diamond.Ty Data))}
    (entry : Tuple (Fact m.value) args) (locals : Locals (Fact m.value) past)
    (current : Wires args past (dataPorts regs)) :
    let compiled := CFG.compileBlock block current
    compiled.outgoing.read entry (evalFacts m entry compiled.flow locals) =
      block.foldl (fun bank q => quadFacts m q bank) (current.read entry locals) := by
  induction block generalizing past with
  | nil => rfl
  | cons q rest ih =>
    simp only [CFG.compileBlock, Loop.Transfer.prepend, evalFacts, List.foldl_cons]
    refine (ih (locals.snoc _) (rebind current q.dest)).trans ?_
    apply congrArg (fun bank => rest.foldl (fun bank q => quadFacts m q bank) bank)
    refine (read_rebind entry locals current q.dest _).trans ?_
    simp only [quadFacts, Quad.inputWires, read_operands]

theorem blockFacts_fold (block : Block Op regs) (entry : Tuple (Fact m.value) (dataPorts regs)) :
    blockFacts m block entry = block.foldl (fun bank q => quadFacts m q bank) entry := by
  exact (compile_eval (past := []) m block entry PUnit.unit (initial regs)).trans
    (congrArg (List.foldl (fun bank q => quadFacts m q bank) · block) (read_initial_tuple entry))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Proofs
