module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Thms

/-! # Simple WIT types and their interpretation: examples

* Simplicity is decided by evaluation: `future` and `stream` anywhere make a type non-simple;
  `own`, `borrow` and `error-context` are simple.
* Values of interpreted types are ordinary Lean values (`rfl`-checked against the
  interpretation): a `record` is a nested product, a `variant` a nested sum, `flags` a bit
  vector, handles their environment's carrier.
* Acceptor sets of WIT values, with soundness against a specification.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT.Examples

open Silmaril.Formats.Accept

/-- No resources. -/
abbrev T := ClosedType Unit

example : (ValType.bytes : T).simple = true := rfl
example : (.record [("a", .prim .u32), ("h", .own ())] : T).simple = true := rfl
example : (.errorContext : T).simple = true := rfl
example : (.stream (some (.prim .u8)) : T).simple = false := rfl
example : (.result (some (.future none)) none : T).simple = false := rfl
example : (.variant [("a", none), ("b", some (.list (.stream none)))] : T).simple = false := rfl

/-- The simple type `list<u8>`. -/
def bytesSimple : SimpleType Empty Unit := ⟨.bytes, rfl⟩

/-- A WIT record `{ id: u32, name: string, tags: list<u8> }`. -/
def person : T := .record [("id", .prim .u32), ("name", .prim .string), ("tags", .bytes)]

example : person.Interp (Env.closed Unit) := ((7 : UInt32), "ada", ([1, 2] : List UInt8), ())

/-- `result<u64, string>`: `inl` is `ok`. -/
example : (ValType.result (some (.prim .u64)) (some (.prim .string)) : T).Interp (Env.closed Unit) :=
  .inl (1 : UInt64)

/-- `variant { none, some(s32) }`. -/
example : (ValType.variant [("none", none), ("some", some (.prim .s32))] : T).Interp
    (Env.closed Unit) := .inr (.inl (-3 : Int32))

/-- `enum` cases are `Fin n`, `flags` bit vectors (bit `i` is label `i`). -/
example : (ValType.enum ["a", "b", "c"] : T).Interp (Env.closed Unit) := (2 : Fin 3)
example : (ValType.flags ["r", "w"] : T).Interp (Env.closed Unit) := (0b10 : BitVec 2)

/-- `list<u8, 4>` is a vector of four bytes. -/
example : (ValType.fixedList (.prim .u8) 4 : T).Interp (Env.closed Unit) := #v[1, 2, 3, 4]

/-- Handles: table indices (`Env.handles`), representations (`Env.reps`), or an abstract
carrier per resource (`Env.abstract`). -/
example : (ValType.own () : T).Interp (Env.closed Unit) := (3 : UInt32)
example : (ValType.borrow () : T).Interp (Env.reps Empty.elim) := (3 : Nat)
example : (ValType.own () : T).Interp (Env.abstract Empty.elim (fun _ => String) Unit) := "file"

/-- A named type is its environment's interpretation. -/
example : (ValType.ref "id" : NamedType Unit).Interp (Env.handles fun _ => UInt64) := (5 : UInt64)

/-! ## Acceptor sets of values -/

/-- The even `u32`s. -/
def evenU32 : ValLang (Env.closed Unit) (.prim .u32 : T) := {x : UInt32 | x % 2 = 0}

/-- The multiples of four. -/
def mult4 : ValLang (Env.closed Unit) (.prim .u32 : T) := {x : UInt32 | x % 4 = 0}

/-- Accepting multiples of four is sound for the even specification. -/
example : Lang.Sound mult4 evenU32 := by
  intro x (hx : x % 4 = 0)
  show x % 2 = 0
  have : x.toNat % 4 = 0 := by simpa [UInt32.toNat_inj] using congrArg UInt32.toNat hx
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_mod, UInt32.reduceToNat]
  omega

/-- The `list<u8>` acceptors are byte languages: the strings starting with `0x7f`. -/
def elfish : ValLang (Env.closed Unit) (.bytes : T) := {bs : List UInt8 | bs.head? = some 0x7f}

example : elfish.toByteLang.Accepts (ByteArray.mk #[0x7f, 0x45]) := by
  show [(0x7f : UInt8), 0x45].head? = some 0x7f
  rfl

/-- String acceptors give byte languages through UTF-8. -/
example : ValLang.utf8 ({"hi"} : ValLang (Env.closed Unit) (.prim .string : T)) = {[104, 105]} := by
  simp only [ValLang.utf8, ByteLang.ofEncoding, Set.image_singleton, utf8]
  exact congrArg _ (by decide +kernel : "hi".toUTF8.data.toList = [104, 105])

end Silmaril.Wasm.Component.WIT.Examples
