module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.InstructionMap.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.SSA.LambdaRTL (CFG Op)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {F G L : Type} {s : PrimitiveSignature F} {t : PrimitiveSignature G}
  {types : L → PacketType} (rename : s.Renaming t)

private theorem branch_map {Γ : List PacketType} (branch : Branch types Γ) :
    (branch.compile (F := F)).mapOp rename.opcode = branch.compile := by
  induction branch <;> simp_all [Branch.compile, CFG.Term.mapOp, Op.mapOp]

private theorem cast_type {Γ : List PacketType} {a b : PacketType} (eq : a = b) (v : Expr Γ a) :
    (cast (congrArg (Expr Γ) eq) v).compile = v.compile := by
  subst b
  rfl

private theorem cast_reply {Γ : List PacketType} {a b ty : PacketType} (eq : a = b) (v : Expr (a :: Γ) ty) :
    (cast (congrArg (fun x => Expr (x :: Γ) ty) eq) v).compile = v.compile := by
  subst b
  rfl

theorem code_compile_map {Γ : List PacketType} (code : Code s types Γ) :
    (code.mapOpcode rename).compile = code.compile.mapOp rename.opcode := by
  induction code with
  | term branch => simp [Code.mapOpcode, Code.compile, CFG.Body.mapOp, branch_map rename]
  | unpack value rest ih => simp [Code.mapOpcode, Code.compile, CFG.Body.mapOp, Op.mapOp, ih]
  | apply op arg target next =>
    simp only [Code.mapOpcode, Code.compile, CFG.Body.mapOp, CFG.Term.mapOp, Op.mapOp]
    rw [cast_type (rename.argument op).symm, cast_reply (rename.reply op).symm]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
