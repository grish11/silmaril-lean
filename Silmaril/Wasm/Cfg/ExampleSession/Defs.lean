module

public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.Cfg.Session.Defs

/-!
# The CFG session of a host-free instance: regression fixtures (definitions)

A validated module with no imports and two exported functions:

```wat
(module
  (type (func))
  (type (func (result i32)))
  (func (type 0) unreachable)       ;; export 0: traps
  (func (type 1) (i32.const 7)))    ;; export 1: answers 7
```

`sesInst` is the scalar instance with no imports whose exports `0`, `1` are the functions `0`, `1`
of `sesStore`, the store the executable instantiation `sesPrep` allocates into the empty store.

* `trapQ`, `valQ`: the questions to exports `0` and `1` (no arguments); `seven`: the typed answer
  `7`.
* `altQ k`, `altR k`: the rounds of the play alternating a trap of export `0` (which resumes from
  the store the trap left) with the answer `7` of export `1`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleSession

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp.ExampleX
open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Abstract.InstSession (Res)

/-- The example module. -/
def sesMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.unreachable]⟩, ⟨⟨1⟩, [], [.intConst .i32 7]⟩]

/-- The executable instantiation of `sesMod` into the empty store. -/
def sesPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) sesMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `sesMod`. -/
def sesStore : Store Nat := sesPrep.1.store

/-- The scalar instance: no imports, exports `0 : [] → []` and `1 : [] → [i32]`. -/
abbrev sesInst : ScalarInstance where
  imports := []
  exports := [⟨[], []⟩, ⟨[], [.num (.int .i32)]⟩]
  addrs := [0, 1]
  store := sesStore

/-- The question to export `0`. -/
def trapQ : sesInst.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The question to export `1`. -/
abbrev valQ : sesInst.F.Op := ⟨⟨1, by decide⟩, ⟨[], .nil⟩⟩

/-- The answer `7` of export `1`. -/
def seven : Typed [.num (.int .i32)] := ⟨[Val.i32 7], .cons ⟨7, rfl⟩ .nil⟩

/-- The questions of the alternating play: export `0` at even rounds, export `1` at odd ones. -/
def altQ (k : Nat) : sesInst.F.Op := if k % 2 = 0 then trapQ else valQ

/-- The rounds of the alternating play: a trap at even rounds, the answer `7` at odd ones. -/
def altR (k : Nat) : List (Call sesInst.E) × (Res sesInst.exports ⊕ PUnit) :=
  if k % 2 = 0 then ([], .inr ()) else ([], .inl ⟨valQ, .inl seven⟩)

end Silmaril.Wasm.Cfg.ExampleSession
