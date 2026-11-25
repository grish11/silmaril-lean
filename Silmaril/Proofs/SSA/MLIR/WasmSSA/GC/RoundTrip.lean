module

public import Silmaril.SSA.MLIR.WasmSSA.GC.Defs

public section

namespace Silmaril.Proofs.SSA.MLIR.WasmSSA.GC

open Silmaril.MLIR.WasmSSA
open Silmaril.MLIR.WasmSSA.GC (ValType embedRef projectRef embed project?)

private theorem project_embedRef {Γ : List IntType} {t : IntType} (ref : Ref Γ t) :
    projectRef (embedRef ref) = ref := by
  induction ref with
  | here => rfl
  | there ref ih => exact congrArg Ref.there ih

private theorem embed_projectRef {Γ : List IntType} {t : IntType}
    (ref : Ref (Γ.map ValType.core) (.core t)) : embedRef (projectRef ref) = ref := by
  induction Γ with
  | nil => cases ref
  | cons s Γ ih =>
      cases ref with
      | here => rfl
      | there ref => exact congrArg Ref.there (ih ref)

private theorem project_embedOp {params Γ : List IntType} {t : IntType}
    (op : Rhs params Γ t) : (op.map embedRef).map projectRef = op := by
  cases op <;> simp only [Op.map, project_embedRef]

private theorem embed_projectOp {params Γ : List IntType} {t : IntType}
    (op : Op params (fun t => Ref (Γ.map ValType.core) (.core t)) t) :
    (op.map projectRef).map embedRef = op := by
  cases op <;> simp only [Op.map, embed_projectRef]

theorem project_embed {params Γ : List IntType} {result : IntType}
    (block : Block params result Γ) : project? (embed block) = some block := by
  induction block with
  | return_ result => simp only [embed, project?, project_embedRef]
  | letOp rhs rest ih => simp only [embed, project?, ih, Option.map_some, project_embedOp]

theorem embed_of_project {params Γ : List IntType} {result : IntType}
    {block : Silmaril.MLIR.WasmSSA.GC.Block params (.core result) (Γ.map ValType.core)}
    {core : Block params result Γ} (h : project? block = some core) :
    embed core = block := by
  match block with
  | .return_ value =>
      simp only [project?, Option.some.injEq] at h
      rw [← h]
      simp only [embed, embed_projectRef]
  | .letOp (.core (t := t) op) rest =>
      cases hrest : project? (Γ := t :: Γ) rest with
      | none => simp [project?, hrest] at h
      | some restCore =>
          have ih := embed_of_project (Γ := t :: Γ) hrest
          simp only [project?, hrest, Option.map_some, Option.some.injEq] at h
          rw [← h]
          simp only [embed, ih, embed_projectOp]
  | .letOp .refNullI31 _ | .letOp (.refIsNull _) _
  | .letOp (.refI31 _) _ | .letOp (.i31GetU _) _ => simp [project?] at h

end Silmaril.Proofs.SSA.MLIR.WasmSSA.GC
