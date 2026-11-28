module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.InstructionMap.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.InstructionMap

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {F G L : Type} {s : PrimitiveSignature F} {t : PrimitiveSignature G}
  {types : L → PacketType} (rename : s.Renaming t)

theorem Code.compile_mapOpcode {Γ : List PacketType} (code : Code s types Γ) :
    (code.mapOpcode rename).compile = code.compile.mapOp rename.opcode :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.code_compile_map rename code

theorem Program.compile_mapOpcode {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    (program : Program s inputs outputs) (i : Fin a) :
    (program.mapOpcode rename).compile i = (program.compile i).mapOp rename.opcode := by
  simp [Program.mapOpcode, Program.compile, Silmaril.SSA.LambdaRTL.CFG.mapOp, List.map_map,
    Function.comp_def, Silmaril.SSA.LambdaRTL.CFG.Block.mapOp, Code.compile_mapOpcode,
    Silmaril.SSA.LambdaRTL.CFG.Body.mapOp, Silmaril.SSA.LambdaRTL.CFG.Term.mapOp]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
