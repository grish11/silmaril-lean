module

public import Silmaril.Wasm.Profiles.Functional.Defs

public section

namespace Silmaril.Proofs.Wasm.Profiles.FunctionalISA

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Models
open Silmaril.Wasm.Profiles Silmaril.Wasm.Profiles.FunctionalISA

theorem atom_sound {ctx gc inputs outputs} (atom : TypedAtom ctx gc inputs outputs) :
    InstrOk ctx atom.toRaw.erase (.plain inputs outputs) := by
  cases atom with
  | intConst bits => exact .numeric (.intConst .i32 bits)
  | bin width op => exact .numeric (.intBinOp width op.toCore)
  | localGet idx lookup => exact .variable (.localGet lookup)
  | refI31 => exact .reference .refI31
  | refFunc idx lookup declared => exact .reference (.refFunc lookup declared)
  | callRef type lookup signature => exact .callRef lookup signature
  | structNew type lookup fields => exact .reference (.structNew lookup fields)
  | structGet sign type field lookup fields entry packed => exact .reference (.structGet lookup fields entry packed)
  | structSet type field lookup fields entry => exact .reference (.structSet lookup fields entry)
  | brIf0 target => exact .brIf (l := ⟨0⟩) (ts := [.i32]) target

private theorem prepend {ctx : Context} {base inputs outputs results : List CValType} {head : Instr} {tail : Expr}
    (frame : ResultOk ctx.toTypeCtx base) (one : InstrOk ctx head (.plain inputs outputs))
    (rest : InstrsOk ctx tail (.plain (base ++ outputs) results)) :
    InstrsOk ctx (head :: tail) (.plain (base ++ inputs) results) :=
  .seq (InstrsOk.frame (.instr one) frame) (by simp) rest

theorem code_sound {gc ctx inputs outputs} (code : Code gc ctx inputs outputs) :
    InstrsOk ctx code.erase (.plain inputs outputs) := by
  induction code with
  | done ok =>
    simpa only [Code.erase, Code.toRaw, Raw.erase, List.append_nil] using InstrsOk.frame .nil ok
  | cons frame head tail rest => exact prepend frame (atom_sound head) rest
  | blockI32 frame body tail inside outside =>
    simpa only [Code.erase, Code.toRaw, Raw.erase, List.append_nil] using
      prepend frame (.block (bt := .value .i32) (.value (.num (.int .i32))) inside) outside
  | sub code sub valid sound => exact .sub sound sub valid

private theorem atom_feature {gc : GCMode} (atom : Atom gc) (exceptions : ExceptionMode) :
    Instr.InFeat (FunctionalCore.features gc exceptions) atom.erase := by
  cases atom <;> cases exceptions <;> first | rfl | (cases ‹GCMode› <;> rfl)

private theorem block_feature (gc : GCMode) (exceptions : ExceptionMode) :
    Instr.headB (FunctionalCore.features gc exceptions) (.block (.value .i32) []) = true := by
  cases gc <;> cases exceptions <;> rfl

private theorem both {left right : Bool} (leftTrue : left = true) (rightTrue : right = true) :
    (left && right) = true := by simp [leftTrue, rightTrue]

theorem raw_features {gc : GCMode} (raw : Raw gc) (exceptions : ExceptionMode) :
    Instr.insInFeatB (FunctionalCore.features gc exceptions) raw.erase = true := by
  induction raw with
  | done => rfl
  | cons head tail rest =>
    exact both (atom_feature head exceptions) rest
  | blockI32 body tail inside outside =>
    exact both (both (block_feature gc exceptions) inside) outside

theorem allowWrites_erase (raw : Raw .immutable) : raw.allowWrites.erase = raw.erase := by
  induction raw with
  | done => rfl
  | cons head tail rest =>
    have headEq : head.allowWrites.erase = head.erase := by cases head <;> rfl
    simp only [Raw.allowWrites, Raw.erase, headEq, rest]
  | blockI32 body tail inside outside => simp only [Raw.allowWrites, Raw.erase, inside, outside]

end Silmaril.Proofs.Wasm.Profiles.FunctionalISA
