module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {F G L : Type} {s : PrimitiveSignature F} {t : PrimitiveSignature G}
  {types : L → PacketType}

/-- An opcode map that preserves the exact argument and reply types. -/
structure PrimitiveSignature.Renaming (s : PrimitiveSignature F) (t : PrimitiveSignature G) where
  opcode : F → G
  argument (op : F) : t.argument (opcode op) = s.argument op
  reply (op : F) : t.reply (opcode op) = s.reply op

variable (rename : s.Renaming t)

/-- Only opcode occurrences change. All typed packet and control positions
stay fixed, including the reply slot used by the continuation. -/
def Code.mapOpcode : {Γ : List PacketType} → Code s types Γ → Code t types Γ
  | _, .term branch => .term branch
  | _, .unpack value tail => .unpack value (tail.mapOpcode)
  | Γ, .apply op arg target next =>
    .apply (rename.opcode op) (cast (congrArg (Expr Γ) (rename.argument op).symm) arg)
      target (cast (congrArg (fun ty => Expr (ty :: Γ) (types target)) (rename.reply op).symm) next)

def Program.mapOpcode {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    (program : Program s inputs outputs) : Program t inputs outputs :=
  ⟨program.locals, program.localType, program.entry, program.entryType, fun i => (program.block i).mapOpcode rename⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
