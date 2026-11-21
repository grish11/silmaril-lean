module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Thms
public import Silmaril.Wasi.Component.Accept.Ref.Examples
public meta import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public meta import Silmaril.Wasi.Component.Accept.Ref.Examples

/-! # The typed environment: examples

* **Kernel-checked runs** (`decide +kernel`, 64 KiB memories): `exportCallArgs_ill` (the
  spurious untyped acceptance), `exportCallTyped_ill` (refused), `exportCallTyped_hi`,
  `exportCallTyped_hi2`, `recordsTyped_hi`, `recordsTyped_ill`. The `#guard`s stay as native
  regressions.
* **Kernel-checked** (`decide +kernel`): the argument check accepts `[list<u8> "hi!"]` at
  `func(bs: list<u8>) -> bool`. It rejects the ill-typed `[list [u32 300, u8 1, u8 2]]`, a
  `string`, and wrong arities.
* **Spurious untyped acceptance** (`#guard`): the exported `len == 3` acceptor
  (`Ref.Examples.exportLen3Bytes`) returns `true` on the ill-typed `[list [u32 300, u8 1, u8 2]]`.
  The typed driver refuses that call (`exportCallTyped … = none`) and still returns `true` on
  `"hi!"`.
* **Imported `accept`** (`acceptHiBytes`): the typed driver records `"hi!"` when `run` is
  called with no arguments. It refuses `run` on an extra argument, which the untyped driver
  makes (`recordsUntyped`).
* **Defaults** (kernel, `rfl`): `bytesSystem` is the typed system; the deprecated
  `refBytesSystem` and `refTypedBytesSystem` are the untyped and typed systems.
* **`tuple<u8, u8>`** (`tupleHiBytes`, lowered with no memory): REF and the IR lowering both read
  it (kernel). REF passes `accept` a *record*, so the `list<u8>` notion `AcceptedTyped` cannot
  see it, while `AcceptedTypedBytes` (through `bytesOf?`, the IR's reading) does.
  `tupleHi_accepts` is a fully **kernel-checked** end-to-end acceptance of `"hi"`: decoding,
  validation, instantiation and the call all run on the Core 3.0 engine in the kernel
  (`tupleRunBytes_eq`). No linear memory is involved.
* **Re-exported `accept`** (`reexportBytes`, a component that imports `accept` and exports it
  unchanged): the typed driver records any `list<u8>` the host passes through the export, here
  `"xyz"`. This is the intended semantics (`Typed/Defs.lean`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

/-- `func(bs: list<u8>) -> bool`. -/
def listBoolFT : WIT.FuncType Empty RtId := ⟨[("bs", .list (.prim .u8))], some (.prim .bool), false⟩

/-- The ill-typed list `[u32 300, u8 1, u8 2]`. -/
def illList : Value.Val := .list [.int .u32 300, .int .u8 1, .int .u8 2]

example : argsTyped listBoolFT [bytesVal hi] = true := by decide +kernel
example : argsTyped listBoolFT [illList] = false := by decide +kernel
example : argsTyped listBoolFT [.string ⟨⟨"hi!", .utf8, 3⟩, .i32⟩] = false := by decide +kernel
example : argsTyped listBoolFT [] = false := by decide +kernel
example : argsTyped listBoolFT [bytesVal hi, bytesVal hi] = false := by decide +kernel

/-- Call the exported `accept` of `exportLen3Bytes` on `args`, untyped: the returned `bool`. -/
def exportCallArgs (args : List Value.Val) : Option Bool :=
  match decodeValid (prof := first.prof) exportLen3Bytes with
  | none => none
  | some a =>
    match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).instantiateRun first 4000
        a.comp [] (Silmaril.Wasm.Component.Reference.initConfig []) with
    | none => none
    | some (r₁, _, es) =>
      match es.lookup "accept" with
      | none => none
      | some f =>
        match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).callTop first 4000 ⟨0⟩ f
            args r₁.config with
        | none => none
        | some r =>
          match callOutcome? ⟨0⟩ r with
          | some (.resolved (some [.bool b])) => some b
          | _ => none

/-- The same call in the typed environment: refused unless `[list<u8> w]` has the export's
parameter types and its result is a `bool`. -/
def exportCallTyped (args : List Value.Val) : Option Bool :=
  match decodeValid (prof := first.prof) exportLen3Bytes with
  | none => none
  | some a =>
    match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).instantiateRun first 4000
        a.comp [] (Silmaril.Wasm.Component.Reference.initConfig []) with
    | none => none
    | some (r₁, _, es) =>
      match es.lookup "accept" with
      | none => none
      | some f =>
        match funcFT? r₁.config f with
        | none => none
        | some ft =>
          if argsTyped ft args && (match ft.result with | some (.prim .bool) => true | _ => false)
          then
            match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).callTop first 4000 ⟨0⟩
                f args r₁.config with
            | none => none
            | some r =>
              match callOutcome? ⟨0⟩ r with
              | some (.resolved (some [.bool b])) => some b
              | _ => none
          else none

-- The untyped environment accepts an ill-typed list: a spurious run.
#guard exportCallArgs [illList] == some true
-- The typed environment refuses it, and still accepts `"hi!"`.
#guard exportCallTyped [illList] == none
#guard exportCallTyped [bytesVal hi] == some true
#guard exportCallTyped [bytesVal [0x68, 0x69]] == some false

/-- Did the typed driver record `[list<u8> w]` on `bytes` after `calls`? -/
def recordsTyped (bytes : ByteArray) (calls : List (String × List Value.Val)) (w : List UInt8) :
    Option Bool :=
  (decodeValid (prof := first.prof) bytes).bind fun a =>
    (acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
      calls).map fun st => st.any fun args => Value.Val.beqList args [bytesVal w]

#guard recordsTyped acceptHiBytes [("run", [])] hi == some true
#guard recordsTyped acceptHiBytes [("run", [.int .u32 5])] hi == none

/-! Kernel-checked versions (`decide +kernel`, 64 KiB memories, `Memory.writeSlice`). -/

/-- The untyped environment's spurious acceptance of an ill-typed list, proved. -/
theorem exportCallArgs_ill : exportCallArgs [illList] = some true := by decide +kernel
/-- The typed environment refuses it ... -/
theorem exportCallTyped_ill : exportCallTyped [illList] = none := by decide +kernel
/-- ... and returns `true` on `"hi!"` and `false` on `"hi"`. -/
theorem exportCallTyped_hi : exportCallTyped [bytesVal hi] = some true := by decide +kernel
theorem exportCallTyped_hi2 : exportCallTyped [bytesVal [0x68, 0x69]] = some false := by
  decide +kernel
/-- The imported acceptor in the typed environment records `"hi!"`, and refuses an ill-typed
call of `run`. -/
theorem recordsTyped_hi : recordsTyped acceptHiBytes [("run", [])] hi = some true := by
  decide +kernel
theorem recordsTyped_ill : recordsTyped acceptHiBytes [("run", [.int .u32 5])] hi = none := by
  decide +kernel

/-- Did the untyped driver record `[list<u8> w]` on `bytes` after `calls`? -/
def recordsUntyped (bytes : ByteArray) (calls : List (String × List Value.Val))
    (w : List UInt8) : Option Bool :=
  (decodeValid (prof := first.prof) bytes).bind fun a =>
    (acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
      calls).map fun st => st.any fun args => Value.Val.beqList args [bytesVal w]

-- The untyped driver makes the ill-typed call that the typed one refuses (`some`, not `none`);
-- here the machine then records nothing.
#guard recordsUntyped acceptHiBytes [("run", [])] hi == some true
#guard recordsUntyped acceptHiBytes [("run", [.int .u32 5])] hi == some false

/-! ### The default bytes system is typed; the former names are deprecated aliases -/

example (prof : ProfileKind) : bytesSystem prof = bytesSystemWith EnvPolicy.typed prof := rfl
example (prof : ProfileKind) : bytesSystem prof ≤ bytesSystemUntyped prof := bytesSystem_le_untyped

set_option linter.deprecated false in
example (prof : ProfileKind) : refBytesSystem prof = bytesSystemUntyped prof := rfl

set_option linter.deprecated false in
example (prof : ProfileKind) : refTypedBytesSystem prof = bytesSystem prof := rfl

/-- `(component (import "accept" (func $a (param "bs" (list u8)))) (export "accept" (func $a)))`
(assembled and validated with `wasm-tools` 1.263.0, stripped). -/
def reexportBytes : ByteArray := ⟨#[0, 97, 115, 109, 13, 0, 1, 0, 7, 11, 2, 112, 125, 64, 1, 2,
  98, 115, 0, 1, 0, 10, 11, 1, 0, 6, 97, 99, 99, 101, 112, 116, 1, 1, 11, 12, 1, 0, 6, 97, 99, 99,
  101, 112, 116, 1, 0, 0]⟩

theorem decodeValid_reexport : (decodeValid (prof := first.prof) reexportBytes).isSome = true := by
  decide +kernel

-- The re-exported `accept` records what the host passes through it.
#guard recordsTyped reexportBytes [("accept", [bytesVal [0x78, 0x79, 0x7a]])] [0x78, 0x79, 0x7a]
  == some true

/-- `"hi!"` is accepted in the default (typed) bytes system, given the typed run that `#guard`
checks. -/
theorem hi_mem_typed_of_run
    (h : ∃ a st, decodeValid (prof := first.prof) acceptHiBytes = some a ∧
      acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
        [("run", [])] = some st ∧ [bytesVal hi] ∈ st) :
    bytesSystem first.prof acceptHiBytes hi :=
  let ⟨_, _, hd, hr, hw⟩ := h
  bytesSystem_of_run first hd hr hw

/-! ## A `tuple<u8, u8>` acceptor: the fragment both semantics read -/

/-- `accept: func(bs: tuple<u8, u8>)` imported and lowered with no memory; `run` calls
`accept(104, 105)` (assembled and validated with `wasm-tools` 1.263.0, stripped). -/
def tupleHiBytes : ByteArray := ⟨#[0, 97, 115, 109, 13, 0, 1, 0, 7, 13, 2, 111, 2, 125, 125, 64,
  1, 2, 98, 115, 0, 1, 0, 10, 11, 1, 0, 6, 97, 99, 99, 101, 112, 116, 1, 1, 8, 5, 1, 1, 0, 0, 0, 1,
  62, 0, 97, 115, 109, 1, 0, 0, 0, 1, 9, 2, 96, 2, 127, 127, 0, 96, 0, 0, 2, 14, 1, 3, 101, 110,
  118, 6, 97, 99, 99, 101, 112, 116, 0, 0, 3, 2, 1, 1, 7, 7, 1, 3, 114, 117, 110, 0, 1, 10, 12, 1,
  10, 0, 65, 232, 0, 65, 233, 0, 16, 0, 11, 2, 21, 2, 1, 1, 6, 97, 99, 99, 101, 112, 116, 0, 0, 0,
  0, 1, 3, 101, 110, 118, 18, 0, 7, 5, 1, 64, 0, 1, 0, 6, 9, 1, 0, 0, 1, 1, 3, 114, 117, 110, 8, 6,
  1, 0, 0, 1, 0, 2, 11, 9, 1, 0, 3, 114, 117, 110, 1, 1, 0]⟩

/-- Both semantics read it: REF decodes and validates it ... -/
theorem decodeValid_tupleHi : (decodeValid (prof := first.prof) tupleHiBytes).isSome = true := by
  decide +kernel

/-- ... and so does the component IR's lowering. -/
theorem decodeBinary_tupleHi :
    (Silmaril.Wasi.Accept.ComponentAcceptor.decodeBinary tupleHiBytes).isSome = true := by
  decide +kernel

/-- `accept: func(bs: tuple<u8, u8>)`: the host supplies `accept` at the component's import type. -/
def tupleFT : WIT.FuncType Empty RtId := ⟨[("bs", .tuple [.prim .u8, .prim .u8])], none, false⟩

/-- The typed run: `accept` received `[record [u8 104, u8 105]]` (a record, not a list). -/
def tupleRun : Option AcceptSt :=
  (decodeValid (prof := first.prof) tupleHiBytes).bind fun a =>
    acceptRunTyped (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 400 a.comp
      [("run", [])] tupleFT

/-- The recorded argument lists, read through `bytesOf?`. -/
def tupleRunBytes : Option (List (Option (List UInt8))) := tupleRun.map (·.map bytesOf?)

theorem tupleRunBytes_eq : tupleRunBytes = some [some [104, 105]] := by
  decide +kernel

/-- **A kernel-checked end-to-end acceptance**: the `tuple<u8, u8>` binary accepts `"hi"`,
read through `bytesOf?`, in the typed environment over the Core 3.0 engine. -/
theorem tupleHi_accepts :
    ∃ a, decodeValid (prof := first.prof) tupleHiBytes = some a ∧
      AcceptedTypedBytes tupleFT first.prof a.comp [104, 105] := by
  have h := tupleRunBytes_eq
  unfold tupleRunBytes tupleRun at h
  obtain ⟨st, hst, hmap⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨args, hargs, hb⟩ : ∃ args ∈ st, bytesOf? args = some [104, 105] := by
    have : some [104, 105] ∈ st.map bytesOf? := by rw [hmap]; simp
    obtain ⟨args, h₁, h₂⟩ := List.mem_map.mp this
    exact ⟨args, h₁, h₂⟩
  exact ⟨a, ha, args, recordsTyped_of_run _ first hr hargs, hb⟩

end Silmaril.Wasi.Accept.Ref.Examples
