module

public import Silmaril.Wasi.Component.Defs
public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Games.Accept.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

/-! # Inputs accepted by a component

A component is a model of its world (`Silmaril.Wasi.World.Model`): a strategy whose imports
are uninterpreted, so its plays range over every behaviour of every host and every caller of
its exports. Its events are the named `WEv`s of `Silmaril.Wasi.World` (`wtrace`). Two
acceptance readings, both existential over plays:

* **Through an imported `accept: func(list<u8>)`** (`importAccepted`): the arguments of some
  call the component makes to the import `f` (`WEv.req f args`), under whatever interaction
  (export calls, answers of other imports) led there.
* **Through an exported `accept: func(list<u8>) -> bool`** (`exportAccepted`): the arguments
  of some call of the export `f` that returns `true` (`WEv.ret f args (some [.bool true])`):
  the *possibility* of `true`, so a nondeterministic component accepts an input when one of
  its behaviours does.

Arguments are decoded by a WIT type (`decode t`), following the value encodings of
`Silmaril.Wasi.Theory` for `Silmaril.Wasm.Component.Val` (which has no lists, strings or
handles): `list<T>`, `list<T, N>`, `record`, `tuple`, `string` (as `char`s) and `map` (as
two-field records) are records; `variant` case `i` is `.variant i payload`, `enum` case `i`
is `.variant i none`, `option` is the variant `none | some(T)` and `result` the variant
`ok(T) | error(E)`; handles (`own`, `borrow`) and `error-context` are their `u32` table index
(`Env.closed`); `flags` with `n` labels is a record of `n` `bool`s. Decoding is strict: any
other shape is rejected.

* `bytesLang σ f` / `exportBytesLang σ f`: the byte languages, through `list<u8>`.
* `valLang t σ f` / `exportValLang t σ f`: the acceptor set of WIT values of type `t`.
* `importAccepted` / `exportAccepted`: the general forms, for any argument decoder.

Equivalence: acceptance only reads the named traces `wtrace '' σ.plays` (`Traces`); components
with the same named traces accept the same inputs (`Silmaril.Wasi.Accept.importAccepted_eq_of_traces`),
equal strategies a fortiori, and IR components that are `CompEquiv` have equal acceptor sets
under any layout (`Silmaril.Wasi.Accept.importAccepted_compModel_of_compEquiv`).

New definitions (no source). The world, event and layout vocabulary is
`Silmaril.Wasi.World` and `Silmaril.Wasi.Component`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.WIT

universe v

/-! ## Decoding WASI values -/

/-- The fields of a record value. -/
def ofRecord? : Val → Option (List Val)
  | .record vs => some vs
  | _ => none

/-- The case and payload of a variant value. -/
def ofVariant? : Val → Option (Nat × Option Val)
  | .variant i p => some (i, p)
  | _ => none

/-- A `u32` value (a handle's table index). -/
def ofU32? : Val → Option (BitVec 32)
  | .u32 x => some x
  | _ => none

/-- A `char` value. -/
def ofChar? : Val → Option Char
  | .char c => some c
  | _ => none

/-- A primitive value. -/
def decodePrim : (p : Primitive) → Val → Option p.Interp
  | .bool, .bool b => some b
  | .u8, .u8 x => some (UInt8.ofBitVec x)
  | .u16, .u16 x => some (UInt16.ofBitVec x)
  | .u32, .u32 x => some (UInt32.ofBitVec x)
  | .u64, .u64 x => some (UInt64.ofBitVec x)
  | .s8, .s8 x => some (Int8.ofBitVec x)
  | .s16, .s16 x => some (Int16.ofBitVec x)
  | .s32, .s32 x => some (Int32.ofBitVec x)
  | .s64, .s64 x => some (Int64.ofBitVec x)
  | .f32, .f32 x => some x
  | .f64, .f64 x => some x
  | .char, .char c => some c
  | .string, .record vs => (vs.mapM ofChar?).map String.ofList
  | _, _ => none

/-- A `list<u8>` value: a record of `u8`s (`bytesV`). -/
def bytes? (v : Val) : Option (List UInt8) := (ofRecord? v).bind (·.mapM (decodePrim .u8))

/-- A `bool` field of a `flags` record. -/
def flagBit? : Val → Option Bool
  | .bool b => some b
  | _ => none

variable {R : Type v}

mutual
/-- **Decode a WASI value at a closed WIT type**, handles as table indices. -/
def decode : (t : ClosedType R) → Val → Option (t.Interp (Env.closed R))
  | .prim p => decodePrim p
  | .ref n => nomatch n
  | .list t => fun v => (ofRecord? v).bind (·.mapM (decode t))
  | .fixedList t n => fun v => (ofRecord? v).bind fun vs => (vs.mapM (decode t)).bind fun xs =>
      if h : xs.length = n then some ⟨xs.toArray, by simpa using h⟩ else none
  | .record fs => fun v => (ofRecord? v).bind (decodeFields fs)
  | .tuple ts => fun v => (ofRecord? v).bind (decodeTuple ts)
  | .variant cs => fun v => (ofVariant? v).bind fun p => decodeCases cs p.1 p.2
  | .enum cs => fun v => (ofVariant? v).bind fun
      | (i, none) => if h : i < cs.length then some ⟨i, h⟩ else none
      | _ => none
  | .flags ls => fun v => ((ofRecord? v).bind (·.mapM flagBit?)).bind fun bs =>
      if h : bs.length = ls.length then
        some (show BitVec ls.length from h ▸ BitVec.ofBoolListLE bs) else none
  | .option t => fun v => (ofVariant? v).bind fun
      | (0, none) => some none
      | (1, some w) => (decode t w).map some
      | _ => none
  | .result ok err => fun v => (ofVariant? v).bind fun
      | (0, p) => (decodeOpt ok p).map Sum.inl
      | (1, p) => (decodeOpt err p).map Sum.inr
      | _ => none
  | .map k t => fun v => (ofRecord? v).bind (·.mapM fun e => (ofRecord? e).bind fun
      | [a, b] => do return (← decodePrim k.toPrimitive a, ← decode t b)
      | _ => none)
  | .own _ | .borrow _ | .errorContext => fun v => (ofU32? v).map UInt32.ofBitVec
  | .future _ | .stream _ => fun _ => none

/-- Decode record fields, in order. -/
def decodeFields : (fs : List (String × ClosedType R)) → List Val →
    Option (ValType.InterpFields (Env.closed R) fs)
  | [], [] => some ()
  | (_, t) :: fs, v :: vs => do return (← decode t v, ← decodeFields fs vs)
  | _, _ => none

/-- Decode tuple components, in order. -/
def decodeTuple : (ts : List (ClosedType R)) → List Val →
    Option (ValType.InterpList (Env.closed R) ts)
  | [], [] => some ()
  | t :: ts, v :: vs => do return (← decode t v, ← decodeTuple ts vs)
  | _, _ => none

/-- Decode variant case `i` with its payload. -/
def decodeCases : (cs : List (String × Option (ClosedType R))) → Nat → Option Val →
    Option (ValType.InterpCases (Env.closed R) cs)
  | [], _, _ => none
  | (_, o) :: _, 0, p => (decodeOpt o p).map Sum.inl
  | _ :: cs, i + 1, p => (decodeCases cs i p).map Sum.inr

/-- Decode an optional payload: present exactly when the type is. -/
def decodeOpt : (o : Option (ClosedType R)) → Option Val →
    Option (ValType.InterpOpt (Env.closed R) o)
  | none, none => some ()
  | some t, some v => decode t v
  | _, _ => none
end

/-- Exactly one argument, decoded by `d`. -/
def args1 {α : Type} (d : Val → Option α) : List Val → Option α
  | [v] => d v
  | _ => none

/-! ## Observations and accepted sets -/

/-- The default acceptor function: `accept`, a function of the world itself. -/
def acceptFn : FnName := ⟨"", "accept"⟩

/-- A call the component makes to the import `f`, its arguments decoded by `dec`. -/
def importObs {α : Type} (f : FnName) (dec : List Val → Option α) : WEv → Option α
  | .req g args => if g = f then dec args else none
  | _ => none

/-- A call of the export `f` returning `true`, its arguments decoded by `dec`. -/
def exportObs {α : Type} (f : FnName) (dec : List Val → Option α) : WEv → Option α
  | .ret g args (some [.bool true]) => if g = f then dec args else none
  | _ => none

/-- The named traces of a component. -/
def Traces {I X : Set FnName} (σ : Strategy (nsig I) (nsig X)) : Set (List WEv) :=
  wtrace '' σ.plays

/-- **Inputs accepted through the import `f`**: decoded arguments of some call to `f`. -/
def importAccepted {I X : Set FnName} {α : Type} (σ : Strategy (nsig I) (nsig X)) (f : FnName)
    (dec : List Val → Option α) : Lang α :=
  observed (importObs f dec) (Traces σ)

/-- **Inputs accepted through the export `f`**: decoded arguments of some call to `f` that
returns `true`. -/
def exportAccepted {I X : Set FnName} {α : Type} (σ : Strategy (nsig I) (nsig X)) (f : FnName)
    (dec : List Val → Option α) : Lang α :=
  observed (exportObs f dec) (Traces σ)

/-- The byte language through an imported `accept: func(list<u8>)`. -/
def bytesLang {I X : Set FnName} (σ : Strategy (nsig I) (nsig X)) (f : FnName := acceptFn) :
    ByteLang :=
  importAccepted σ f (args1 bytes?)

/-- The byte language through an exported `accept: func(list<u8>) -> bool`. -/
def exportBytesLang {I X : Set FnName} (σ : Strategy (nsig I) (nsig X))
    (f : FnName := acceptFn) : ByteLang :=
  exportAccepted σ f (args1 bytes?)

/-- The values of the WIT type `t` accepted through an imported `accept: func(t)`. -/
def valLang (t : ClosedType R) {I X : Set FnName} (σ : Strategy (nsig I) (nsig X))
    (f : FnName := acceptFn) : ValLang (Env.closed R) t :=
  importAccepted σ f (args1 (decode t))

/-- The values of the WIT type `t` accepted through an exported `accept: func(t) -> bool`. -/
def exportValLang (t : ClosedType R) {I X : Set FnName} (σ : Strategy (nsig I) (nsig X))
    (f : FnName := acceptFn) : ValLang (Env.closed R) t :=
  exportAccepted σ f (args1 (decode t))

end Silmaril.Wasi.Accept

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept

/-! ## Specification components -/

/-- The byte string `w` as a WASI `list<u8>` value. -/
def bytesVal (w : List UInt8) : Silmaril.Wasm.Component.Val := bytesV (w.map UInt8.toBitVec)

/-- **A component accepting exactly `L` through its import**: on a call of its export `run`
(no arguments), it may call the imported `accept` with any string of `L`. -/
def importAcceptor (L : ByteLang) (run : FnName) : Strategy (nsig {acceptFn}) (nsig {run}) :=
  Strategy.generate {s | ∃ w ∈ L, s = [.inr (.ask (⟨run, rfl⟩, [])),
    .inl (.ask (⟨acceptFn, rfl⟩, [bytesVal w]))]}

/-- **A component accepting exactly `L` through its export**: a call of `accept` with a string
of `L` may return `true`. -/
def exportAcceptor (L : ByteLang) : Strategy (nsig ∅) (nsig {acceptFn}) :=
  Strategy.generate {s | ∃ w ∈ L, s = [.inr (.ask (⟨acceptFn, rfl⟩, [bytesVal w])),
    .inr (.ans (⟨acceptFn, rfl⟩, [bytesVal w]) (some [.bool true]))]}

end Silmaril.Wasi.Accept
