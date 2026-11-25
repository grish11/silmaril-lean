module

public import Silmaril.SSA.MLIR.WasmSSA.Defs

/-! # Project-defined WASM-GC-SSA syntax

The extension adds nullable and non-nullable i31 references and four typed
operation forms. All function parameters remain immutable integer local
references. There is no heap or evaluation relation.
-/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA.GC

inductive ValType where
  | core (type : IntType)
  | nullableI31
  | i31
  deriving DecidableEq, Repr

inductive Rhs (params : List IntType) (Γ : List ValType) : ValType → Type where
  | core {t : IntType} (op : Op params (fun t => Ref Γ (.core t)) t) : Rhs params Γ (.core t)
  | refNullI31 : Rhs params Γ .nullableI31
  | refIsNull (input : Ref Γ .nullableI31) : Rhs params Γ (.core .i32)
  | refI31 (input : Ref Γ (.core .i32)) : Rhs params Γ .i31
  | i31GetU (input : Ref Γ .i31) : Rhs params Γ (.core .i32)

inductive Block (params : List IntType) (result : ValType) : List ValType → Type where
  | return_ {Γ : List ValType} (value : Ref Γ result) : Block params result Γ
  | letOp {Γ : List ValType} {t : ValType} (rhs : Rhs params Γ t)
      (rest : Block params result (t :: Γ)) : Block params result Γ

abbrev Func (params : List IntType) (result : ValType) := Block params result []

def embedRef {Γ : List IntType} {t : IntType} : Ref Γ t → Ref (Γ.map ValType.core) (ValType.core t)
  | .here => .here
  | .there x => .there (embedRef x)

def projectRef {Γ : List IntType} {t : IntType} : Ref (Γ.map ValType.core) (ValType.core t) → Ref Γ t :=
  match Γ with
  | [] => fun x => nomatch x
  | _ :: _ => fun
    | .here => .here
    | .there x => .there (projectRef x)

/-- Embed a whole core block, preserving each binding, operand, and return. -/
def embed {params Γ : List IntType} {result : IntType} :
    WasmSSA.Block params result Γ → Block params (.core result) (Γ.map ValType.core)
  | .return_ value => .return_ (embedRef value)
  | .letOp rhs rest => .letOp (.core (rhs.map embedRef)) (embed rest)

/-- Recover a core block only if every binding is a core operation. A GC
binding makes projection fail even when its result is unused. -/
def project? {params Γ : List IntType} {result : IntType} :
    Block params (.core result) (Γ.map ValType.core) → Option (WasmSSA.Block params result Γ)
  | .return_ value => some (.return_ (projectRef value))
  | .letOp (.core op) rest => (project? rest).map (.letOp (op.map projectRef))
  | .letOp .refNullI31 _ | .letOp (.refIsNull _) _
  | .letOp (.refI31 _) _ | .letOp (.i31GetU _) _ => none

end Silmaril.MLIR.WasmSSA.GC
