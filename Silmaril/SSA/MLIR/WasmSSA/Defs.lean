module

public import Init.Data.BitVec

/-! # The integer WasmSSA fragment

One isolated function body with one integer result. Parameters are immutable
local references. Scalar SSA values are produced by instructions in the block
and scoped by their binding order.
-/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA

inductive IntType where
  | i32 | i64
  deriving DecidableEq, Repr

def IntType.width : IntType → Nat
  | .i32 => 32
  | .i64 => 64

/-- A typed position. Parameter lists are in declaration order and SSA
contexts have the newest binding first. -/
inductive Ref {α : Type} : List α → α → Type where
  | here {Γ : List α} {t : α} : Ref (t :: Γ) t
  | there {Γ : List α} {s t : α} : Ref Γ t → Ref (s :: Γ) t

def Ref.index {α : Type} {Γ : List α} {t : α} : Ref Γ t → Nat
  | .here => 0
  | .there x => x.index + 1

@[simp] theorem Ref.getElem?_index {α : Type} {Γ : List α} {t : α}
    (x : Ref Γ t) : Γ[x.index]? = some t := by
  induction x with
  | here => rfl
  | there x ih => exact ih

inductive BinOp where
  | add | sub | mul | and | or | xor
  deriving DecidableEq, Repr

/-- `Value` determines how operands refer to the surrounding SSA context. This
lets the GC extension share the core operation signatures. -/
inductive Op (params : List IntType) (Value : IntType → Type) : IntType → Type where
  | const {t : IntType} (bits : BitVec t.width) : Op params Value t
  | localGet {t : IntType} (param : Ref params t) : Op params Value t
  | binary {t : IntType} (op : BinOp) (lhs rhs : Value t) : Op params Value t
  | eqz {t : IntType} (input : Value t) : Op params Value .i32
  | select {t : IntType} (condition : Value .i32) (ifTrue ifFalse : Value t) : Op params Value t

def Op.map {params : List IntType} {Value Value' : IntType → Type}
    (f : {t : IntType} → Value t → Value' t) {t : IntType} : Op params Value t → Op params Value' t
  | .const bits => .const bits
  | .localGet param => .localGet param
  | .binary op lhs rhs => .binary op (f lhs) (f rhs)
  | .eqz input => .eqz (f input)
  | .select condition ifTrue ifFalse => .select (f condition) (f ifTrue) (f ifFalse)

abbrev Rhs (params Γ : List IntType) := Op params (Ref Γ)

inductive Block (params : List IntType) (result : IntType) : List IntType → Type where
  | return_ {Γ : List IntType} (value : Ref Γ result) : Block params result Γ
  | letOp {Γ : List IntType} {t : IntType} (rhs : Rhs params Γ t)
      (rest : Block params result (t :: Γ)) : Block params result Γ

/-- The single entry block of a function starts with parameter references and
no scalar SSA bindings. -/
abbrev Func (params : List IntType) (result : IntType) := Block params result []

/-- The types of the SSA bindings in program order. -/
def Block.bindingTypes {params Γ : List IntType} {result : IntType} :
    Block params result Γ → List IntType
  | .return_ _ => []
  | .letOp (t := t) _ rest => t :: rest.bindingTypes

end Silmaril.MLIR.WasmSSA
