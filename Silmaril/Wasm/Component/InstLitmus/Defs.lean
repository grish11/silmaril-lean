module

public import Silmaril.Wasm.Component.InstEngine.Defs

/-!
# Instantiation litmus components

Core 3.0 modules with start functions, and components instantiating them, for the
instantiating denotation `Comp.denI` over the Core 3.0 engine (`Param.core3SemI P`).

Modules (`Reference.ImpModule`):

* `callMod k` (`k = 1, 2`): imports `f: [i32] → []`; its start function is `i32.const k; call 0`
  (it calls the import with `k`); no exports.
* `trapMod`: no imports; its start function is `unreachable`; it exports `get: [] → [i32]`
  returning `7`.
* `getMod`: no imports, no start function; it exports `get: [] → [i32]` returning `7`.
* `globMod`: no imports, a mutable global initialised to `0`; its start function stores `42`
  into it; it exports `get: [] → [i32]` returning the global.

Components, all importing one host function `f: func(u32)` (index `0`):

* `twoC`: `callMod 1` then `callMod 2`, both wired to `f`, no exports (litmus (a): order);
* `oneC`: `callMod 1` wired to `f`, no exports (litmus (b));
* `trapC`: `trapMod`, then `callMod 2` wired to `f`, exporting `trapMod`'s `get`
  (litmus (c));
* `hiddenC`: `callMod 1` wired to `f`, which exports nothing and is never called, then
  `getMod`, whose `get` is exported (litmus (d)).
* `globC`: `globMod`, exporting its `get` (export-phase litmus (e): the start function's write
  is seen by the export);
* `callGlobC`: `callMod 1` wired to `f`, then `globMod`, exporting `globMod`'s `get`
  (export-phase litmus (f): both start functions run in order, then the export is answered);
* `trap1C`: `trapMod` alone, exporting its `get` (export-phase litmus (g)).

Moves: `fQ k` is the host question `f(k)` (flat `i32 k`), `unitA` the answer `()`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.InstLitmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- `(import "env" "f" (func (param i32))) (func $s i32.const k; call 0) (start $s)`. -/
def callCore3 (k : BitVec 32) : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "f", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 k, .call ⟨0⟩]⟩]
  start := some ⟨1⟩

/-- The flat type `[i32] → []` of the import `f`. -/
def fFt : CoreFuncTy := ⟨[.int .i32], []⟩

/-- `callCore3 k` with its interfaces: the import `f`, no exports. -/
def callMod (k : BitVec 32) : ImpModule := ⟨callCore3 k, [("f", fFt)], []⟩

/-- `(func $s unreachable) (func (export "get") (result i32) i32.const 7) (start $s)`. -/
def trapCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.unreachable]⟩, ⟨⟨1⟩, [], [.intConst .i32 7]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]
  start := some ⟨0⟩

/-- The flat type `[] → [i32]` of `get`. -/
def getFt : CoreFuncTy := ⟨[], [.int .i32]⟩

/-- `trapCore3` with its interfaces. -/
def trapMod : ImpModule := ⟨trapCore3, [], [("get", getFt)]⟩

/-- `(func (export "get") (result i32) i32.const 7)`. -/
def getCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 7]⟩]
  exports := [⟨"get", .func ⟨0⟩⟩]

/-- `getCore3` with its interfaces. -/
def getMod : ImpModule := ⟨getCore3, [], [("get", getFt)]⟩

/-- `(global (mut i32) (i32.const 0)) (func $s i32.const 42 global.set 0)
(func (export "get") (result i32) global.get 0) (start $s)`. -/
def globCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 42, .globalSet ⟨0⟩]⟩, ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]
  start := some ⟨0⟩

/-- `globCore3` with its interfaces. -/
def globMod : ImpModule := ⟨globCore3, [], [("get", getFt)]⟩

/-- The host import `f: func(u32)`. -/
def hostI : Iface := [("f", ⟨[.u32], []⟩)]

/-- The export `get: func() -> u32`, implemented by environment function `r`. -/
def getX (r : Nat) : Export := ⟨"get", ⟨[], [.u32]⟩, Impl.fwd r⟩

/-- (a) Two instances whose start functions call `f` with `1` and `2`. -/
def twoC : Comp ImpModule := .mk hostI [.core (callMod 1) [Impl.fwd 0], .core (callMod 2) [Impl.fwd 0]] []

/-- (b) One instance whose start function calls `f` with `1`. -/
def oneC : Comp ImpModule := .mk hostI [.core (callMod 1) [Impl.fwd 0]] []

/-- (c) A trapping start function, then an instance whose start function calls `f`; the first
instance's `get` is exported. -/
def trapC : Comp ImpModule := .mk hostI [.core trapMod [], .core (callMod 2) [Impl.fwd 0]] [getX 1]

/-- (d) An instance without exports that nothing calls, then an instance whose `get` is
exported. -/
def hiddenC : Comp ImpModule := .mk hostI [.core (callMod 1) [Impl.fwd 0], .core getMod []] [getX 1]

/-- (e) An instance whose start function writes a global that its exported `get` reads. -/
def globC : Comp ImpModule := .mk [] [.core globMod []] [getX 0]

/-- (f) `callMod 1`, whose start function calls `f(1)`, then `globMod`, whose `get` is
exported. -/
def callGlobC : Comp ImpModule :=
  .mk hostI [.core (callMod 1) [Impl.fwd 0], .core globMod []] [getX 1]

/-- (g) A trapping start function; its instance's `get` is exported. -/
def trap1C : Comp ImpModule := .mk [] [.core trapMod []] [getX 0]

/-- The export question `get()`, at the component's interface. -/
def getQ : sigU.Op := (0, .flat [])

/-- The question `get()`, at the interface of `globMod`. -/
def getM : (sigN 1).Op := (⟨0, Nat.zero_lt_one⟩, .flat [])

/-- The answer `42` of `get`. -/
def a42 : Option Payload := some (.flat [Flat.i32 42])

/-- The host question `f(k)`. -/
def fQ (k : BitVec 32) : sigU.Op := (0, .flat [Flat.i32 k])

/-- The answer `()` of the host. -/
def unitA : Option Payload := some (.flat [])

end Silmaril.Wasm.Component.InstLitmus
