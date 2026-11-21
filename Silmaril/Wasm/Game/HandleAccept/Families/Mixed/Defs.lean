module

public import Silmaril.Wasm.Game.HandleAccept.Families.Matrix
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Defs
import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Verify.Check.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Families.Mixed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted
open Silmaril.Wasm.Resource (ansOk argsOk runTo?)
open Silmaril.Wasm.Verify (refOracle specInstance?)

private def mixedPairBody : List Instr :=
  [.intConst .i32 16, .intConst .i32 0x61, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .call ⟨0⟩, .localSet ⟨0⟩,
   .intConst .i32 16, .intConst .i32 0x62, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .call ⟨1⟩, .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨2⟩, .call ⟨3⟩]

/-- A n-ary writer that calls distinct atom imports before publishing their list. -/
public def mixedPairMod (first second : String) : Module :=
  { pairAtomMod first with
    imports := [⟨"sexp", first, .func ⟨0⟩⟩, ⟨"sexp", second, .func ⟨0⟩⟩,
      ⟨"sexp", "sexp", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
    funcs := [⟨⟨2⟩, [.i32, .i32], mixedPairBody⟩]
    exports := [⟨"run", .func ⟨4⟩⟩] }

private def hintedConsBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x62616968, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .intConst .i32 2, .intConst .i32 2, .call ⟨0⟩,
   .intConst .i32 4, .intConst .i32 0x63, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .intConst .i32 1, .call ⟨1⟩,
   .call ⟨2⟩, .call ⟨3⟩, .call ⟨3⟩, .call ⟨4⟩]

/-- A cons writer that publishes a tagged atom and a hint-free blob in the same list. -/
public def hintedConsMod : Module :=
  let base := consAtomMod "blob"
  { base with
    types := base.types ++ [tyHinted]
    imports := [⟨"sexp", "hinted", .func ⟨4⟩⟩, ⟨"sexp", "blob", .func ⟨0⟩⟩,
      ⟨"sexp", "nil", .func ⟨3⟩⟩, ⟨"sexp", "cons", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
    funcs := [⟨⟨2⟩, [], hintedConsBody⟩]
    exports := [⟨"run", .func ⟨5⟩⟩] }

private def scratch : ByteArray := ⟨Array.replicate 17 0⟩

private def runWrites {Event : Type} (guest : Module) (inst : ScalarInstance)
    (roles : Roles Unit Event Unit Unit) : List (List Val) → Config Nat → Option (List Event)
  | [], config =>
    if (Exec.runI refOracle 48 config).1.code.isEmpty then some [] else none
  | answer :: rest, config => do
    let (stopped, context, address, target, args) ← runTo? 48 config
    if !(argsOk inst target args && ansOk inst stopped.store address target answer) then none else do
      let observed ← calloutAt? guest (some 0) stopped
      let event ← match roles.callIn observed,
        roles.answerIn observed ⟨.values answer, observed.mem⟩ with
        | some event, none | none, some event => some event
        | _, _ => none
      let later ← runWrites guest inst roles rest
        ⟨stopped.store, stopped.frame, context.fill (vals answer)⟩
      some (event :: later)

/-- Run the actual export and decode its memory callouts. Every scripted answer must typecheck
and produce exactly one writer observation. Overriding the pages with `scratch` is for a small
kernel regression only; it is not a specification instance. -/
private def replay {Event : Type} (guest : Module) (roles : Roles Unit Event Unit Unit)
    (answers : List (List Val)) : Option (List Event) := do
  let (_, inst, _) ← specInstance? guest
  let address ← inst.addrs[0]?
  let memory ← inst.store.mems[0]?
  let store := { inst.store with mems := [{ memory with bytes := scratch }] }
  runWrites guest inst roles answers (invoke store address [])

public def symbolA : Fam.Atom .symStrKwBytes := ⟨.symbol, by decide, "a"⟩
public def stringB : Fam.Atom .symStrKwBytes := ⟨.string, by decide, "b"⟩
public def keywordB : Fam.Atom .symStrKwBytes := ⟨.keyword, by decide, "b"⟩
public def blobA : Fam.Atom .symStrKwBytes := ⟨.bytes, by decide, [0x61]⟩

@[expose] public def mixedPairTrace {Atom : Type} (first second : Atom) : List (WEv (SxOp Atom) (BitVec 32)) :=
  [.write (.atom first) [] 41, .write (.atom second) [] 323, .write .list [41, 323] 5, .accept 5]

public def mixedPairReplay (first second : String) :
    Option (List (WEv (SxOp (Fam.Atom .symStrKwBytes)) (BitVec 32))) :=
  replay (mixedPairMod first second) (tabRoles symStrKwBytesTab {})
    [[.i32 41], [.i32 323], [.i32 5], []]

public def hintedConsReplay : Option (List (WEv (ConsOp Hinted) (BitVec 32))) :=
  replay hintedConsMod (tabConsRoles hintedTab {})
    [[.i32 41], [.i32 323], [.i32 5], [.i32 90], [.i32 101], []]

public def bareBlob : Hinted := (none, [0x63])

@[expose] public def hintedConsTrace : List (WEv (ConsOp Hinted) (BitVec 32)) :=
  [.write (.atom hiabHinted) [] 41, .write (.atom bareBlob) [] 323, .write .nil [] 5,
    .write .cons [323, 5] 90, .write .cons [41, 90] 101, .accept 101]

@[expose] public def hintedConsTree : SExp2 Hinted := .cons (.atom hiabHinted) (.cons (.atom bareBlob) .nil)

private instance {kind : AtomKind} : DecidableEq kind.Val := by cases kind <;> infer_instance
private instance : DecidableEq Hinted := inferInstanceAs (DecidableEq (Option (List UInt8) × List UInt8))

deriving instance DecidableEq for Atom, SxOp, ConsOp, WEv

public theorem symbol_string_trace :
    mixedPairReplay "symbol" "string" = some (mixedPairTrace symbolA stringB) := by decide +kernel

public theorem blob_keyword_trace :
    mixedPairReplay "blob" "keyword" = some (mixedPairTrace blobA keywordB) := by decide +kernel

public theorem hinted_cons_trace : hintedConsReplay = some hintedConsTrace := by decide +kernel

end Silmaril.Wasm.Game.HandleAccept.Families.Mixed
