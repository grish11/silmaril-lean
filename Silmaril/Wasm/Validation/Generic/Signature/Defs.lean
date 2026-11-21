module

public import Silmaril.Wasm.Validation.Generic.Defs

@[expose] public section

namespace Silmaril.Wasm.Generic.Signature

/-- The source interface uses its own type codes, including the representation
of a whole result. It has no embedded Core type-context witness. -/
structure Func (Ty : Type) where
  params : List Ty
  result : Ty

def Func.map {Ty Ty' : Type} (f : Ty → Ty') (sig : Func Ty) : Func Ty' :=
  ⟨sig.params.map f, f sig.result⟩

structure Slot {Ty : Type} (Body : Func Ty → Type) where
  sig : Func Ty
  body : Body sig

def Slot.map {Ty Ty' : Type} {B : Func Ty → Type} {C : Func Ty' → Type} (f : Ty → Ty')
    (lift : ∀ {sig}, B sig → C (sig.map f)) (slot : Slot B) : Slot C :=
  ⟨slot.sig.map f, lift slot.body⟩

/-- This profile has one type declaration per local function slot and named
function exports. Function and type slots remain distinct Core index spaces.
Memory and data declarations do not depend on the choice of type carrier. -/
structure Module {Ty : Type} (Body : Func Ty → Type) where
  defs : List (Slot Body)
  exports : List (String × FuncIdx)
  exportsInScope : ∀ entry ∈ exports, entry.2.toNat < defs.length
  memories : List MemoryType
  data : List Data

def Module.map {Ty Ty' : Type} {B : Func Ty → Type} {C : Func Ty' → Type} (f : Ty → Ty')
    (lift : ∀ {sig}, B sig → C (sig.map f)) (mod : Module B) : Module C :=
  ⟨mod.defs.map (Slot.map f lift), mod.exports, by simpa using mod.exportsInScope, mod.memories, mod.data⟩

def Module.signatureAt? {Ty : Type} {B : Func Ty → Type} (mod : Module B) (index : FuncIdx) :
    Option (Func Ty) := mod.defs[index.toNat]?.map Slot.sig

/-- Partial encoding to numeric Wasm signatures makes all generated singleton
type groups acyclic. It need not encode internal SSA products or sums. -/
structure Encoding (Ty : Type) where
  arg : Ty → Option NumType
  result : Ty → Option (List NumType)

def Func.encode? {Ty : Type} (encoding : Encoding Ty) (sig : Func Ty) : Option FuncType := do
  let params ← sig.params.mapM encoding.arg
  let results ← encoding.result sig.result
  return ⟨params.map .num, results.map .num⟩

def encodeSlots? {Ty Out : Type} {B : Func Ty → Type} (encoding : Encoding Ty)
    (emit : ∀ {sig}, TypeIdx → FuncType → B sig → Option (List ValType × Out)) :
    Nat → List (Slot B) → Option (List (RecType × Generic.Function Out))
  | _, [] => some []
  | index, slot :: rest => do
    let ref ← Idx.ofNat? index
    let type ← slot.sig.encode? encoding
    let (locals, body) ← emit ref type slot.body
    let tail ← encodeSlots? encoding emit (index + 1) rest
    return (⟨[⟨true, [], .func type⟩]⟩, ⟨ref, locals, body⟩) :: tail

/-- Produce the fixed-Core raw generic representation. A successful encoding
does not validate the translated code or other Core declarations. -/
def Module.specialize? {Ty Out : Type} {B : Func Ty → Type} (encoding : Encoding Ty)
    (emit : ∀ {sig}, TypeIdx → FuncType → B sig → Option (List ValType × Out)) (mod : Module B) :
    Option (ModuleParts (Generic.Function Out)) := do
  let entries ← encodeSlots? encoding emit 0 mod.defs
  return ⟨{ types := entries.map Prod.fst,
            exports := mod.exports.map (fun (name, index) => ⟨name, .func index⟩),
            memories := mod.memories, data := mod.data }, entries.map Prod.snd⟩

end Silmaril.Wasm.Generic.Signature
