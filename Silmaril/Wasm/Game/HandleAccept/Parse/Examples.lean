module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Thms

/-!
# Parsing exports: examples

* `wordParse` (import `0 word : [i64] → [i32]`; export `0 parse : [i64] → [i32]`) answers
  `parse(x)` with `word(x)`: a one-shot parser of `i64` data that builds its tree through a
  writer import. It validates and instantiates (`wordParse_instance`); as a one-shot parser it
  relates only one-value inputs (`wordParse_input`). That the related tree is the word `x`
  needs a combined writer and parsing host, which is not defined yet.
* The decoder on concrete export answers: `parse(5) = 7` is `PEv.parse 5 7`
  (`parseDec_parse`), `finish() = (3, 9)` is `PEv.finish 3 9` (`parseDec_finish`), and an
  `append` that traps is no event (`parseDec_append_trap`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Parsing.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Accept.Parse

/-- `[i64] → [i32]`. -/
def tyWord : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩

/-- **A one-shot parser**: `parse(x) = word(x)`. -/
def wordParse : Module where
  types := [tyWord]
  imports := [⟨"sexp", "word", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"parse", .func ⟨1⟩⟩]

/-- Its parsing export. -/
def wordParseIx : ParseExports (BitVec 64) := {val := i64Val, parse := some 0}

theorem wordParse_instance : (Verify.instance? wordParse).isSome = true := by decide +kernel

/-- **`wordParse` relates only one-value inputs** (every profile, environment set and policy
without UB on unresolved handles). -/
theorem wordParse_input {X : Type} (P : Profile) {pol : PPolicy (BitVec 32)}
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) (hb : pol.onBadHandle ≠ .ub) :
    inputLang (moduleParseRel P wordParse wordParseIx pol Envs) ⊆ {w | ∃ v, w = [v]} :=
  moduleParseRel_input_oneShot ⟨rfl, rfl, rfl, rfl⟩ hb

/-! ## The decoder on concrete answers -/

/-- Export types: `0 parse : [i64] → [i32]`, `1 append : [i64] → []`,
`2 finish : [] → [i32 i32]`. -/
def exps : List FnType :=
  [⟨[.num (.int .i64)], [.num (.int .i32)]⟩, ⟨[.num (.int .i64)], []⟩,
   ⟨[], [.num (.int .i32), .num (.int .i32)]⟩]

/-- The exports of `exps`. -/
def expsIx : ParseExports (BitVec 64) :=
  {val := i64Val, parse := some 0, append := some 1, finish := some 2}

/-- The call `parse(5)`. -/
def parse5 : (ifaceSig exps).Op := ⟨⟨0, by decide⟩, ⟨[Val.i64 5], .cons ⟨_, rfl⟩ .nil⟩⟩

/-- The call `append(5)`. -/
def append5 : (ifaceSig exps).Op := ⟨⟨1, by decide⟩, ⟨[Val.i64 5], .cons ⟨_, rfl⟩ .nil⟩⟩

/-- The call `finish()`. -/
def finish0 : (ifaceSig exps).Op := ⟨⟨2, by decide⟩, ⟨[], .nil⟩⟩

theorem parseDec_parse :
    parseDec expsIx parse5 (.values ⟨[Val.i32 7], .cons ⟨_, rfl⟩ .nil⟩) = some (.parse 5 7) :=
  rfl

theorem parseDec_finish :
    parseDec expsIx finish0
        (.values ⟨[Val.i32 3, Val.i32 9], .cons ⟨_, rfl⟩ (.cons ⟨_, rfl⟩ .nil)⟩) =
      some (.finish 3 9) :=
  rfl

theorem parseDec_append :
    parseDec expsIx append5 (.values ⟨[], .nil⟩) = some (.append 5) := rfl

theorem parseDec_append_trap : parseDec expsIx append5 .trap = none := rfl

end Silmaril.Wasm.Game.HandleAccept.Parsing.Examples
