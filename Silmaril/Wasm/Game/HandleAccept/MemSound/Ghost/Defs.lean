module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs
public import Silmaril.Wasm.Component.Reference.HostMap.Thms

/-!
# Memory-observing soundness with ghost state: history-sensitive import contracts

The contracts of `Silmaril.Wasm.Game.HandleAccept.MemSound` (`MemContract`) constrain each callout
on its own: the program logic proves `K.pre o` at every reachable call from the store and the
arguments of that call. A fact relating *several* events of a session (a chunk read by one call,
consumed by a later one) is out of reach: what a host answer tells the module reaches its next
call only through the module's locals and stack, which no import specification sees, and the
admitted hosts may rewrite every global and the whole memory between calls.

This topic threads a **ghost state** `g : G` through the program logic. The ghost lives in the
specification world only, in the **host code** of the store: a real configuration `c`
(`Config Nat`, host function `k` is import `k`) is related to `gConfig g c`, the same
configuration whose host functions carry the code `(k, g)` (`Config.mapH (ghostH g)`, from
`Silmaril.Wasm.Component.Reference.HostMap`). Nothing else changes: memories, globals, tables,
frames, function types and wasm code are the same, and host-free steps commute with the
relabelling (`Step.mapH`), so the module's own steps are unaffected. The most general host of a
contract, `gHost`, reads the ghost of the call from the store, decides the call with `K.pre g`,
and answers in a store relabelled with the ghost moved over the inputs the call and the answer
decode to.

## Ghost contracts

`GContract I G` over decoded inputs `I`:

* `pre g o`: the guarantee at a call, now a predicate on the ghost state `g` of the call and the
  callout `o` (memory at the call);
* `ans x`: the assumption on every input decoded at a host answer (as `MemContract.ans`);
* `reply e a`: the admitted raw replies (as `MemContract.reply`); the admitted environments are
  `ReplyEnvs reply`, unchanged by the ghost;
* `upd g x`: the ghost after the decoded input `x`.

`callGhost R K g o` is the ghost after the input decoded at the call `o` (if any),
`ansGhost R K g o w` after the input decoded at its answer `w`. `tagGhost upd g ts` folds `upd`
over the inputs of a tag list: in a traced session, the ghost of the decoded prefix.

## The obligation

`GMemSat P m memIdx R K Inv g₀`: for the specification instance of `m` (memory `memIdx` at
`memAddr`),

* instantiation is safe under `gHost` from `gConfig g₀ c₀` and, if it returns, returns in a store
  `gStore g s` with `Inv g s` (`gInstPost`);
* every export address `a` meets `gExportSpec Inv a`: from a store `gStore g s` with `Inv g s`
  and arguments `$invoke` accepts in `s`, every outcome ends in a store `gStore g' s'` with
  `Inv g' s'`.

`Inv g s` relates the ghost to the module's store between export calls; since the admitted hosts
may rewrite the store, it is typically a ghost-only bound (for instance "at most 16 values are
buffered") together with the store's shape.

Specialisations: `MemSat` is `GMemSat` for a one-point ghost: `MemContract.toG K` is the ghost
contract over `Unit` with `pre _ = K.pre` (same `ans`, `reply`), and `Thms.memSat_iff_gMemSat`:
`MemSat P m memIdx R K Inv ↔ GMemSat P m memIdx R K.toG (fun _ => Inv) ()`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO
  Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec FSpecValid Safe)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH)

variable {X I O C G : Type}

/-! ## Ghost-carrying stores -/

/-- Host code `k` carrying the ghost `g`. -/
def ghostH (g : G) : Nat → Nat × G := fun k => (k, g)

/-- The store `s` with every host function carrying the ghost `g`. -/
def gStore (g : G) (s : Store Nat) : Store (Nat × G) := Store.mapH (ghostH g) s

/-- The configuration `c` with every host function carrying the ghost `g`. -/
def gConfig (g : G) (c : Config Nat) : Config (Nat × G) := Config.mapH (ghostH g) c

/-! ## Ghost contracts -/

/-- **A ghost contract** of a module's imports, over decoded inputs `I` and ghost states `G`. -/
structure GContract (I G : Type) where
  /-- The guarantee at a call, in the ghost state of the call. -/
  pre : G → Callout → Prop
  /-- The assumption on an input decoded at a host answer. -/
  ans : I → Prop := fun _ => True
  /-- The admitted raw replies. -/
  reply : UCall Nat → UReply → Prop
  /-- The ghost state after a decoded input. -/
  upd : G → I → G

/-- **The one-point ghost contract** of a memory contract: the ghost is `()`, the guarantee
ignores it. -/
def _root_.Silmaril.Wasm.Game.HandleAccept.MemSound.MemContract.toG (K : MemContract I) :
    GContract I Unit where
  pre _ := K.pre
  ans := K.ans
  reply := K.reply
  upd _ _ := ()

/-- The ghost state after an optional decoded input. -/
def GContract.after (K : GContract I G) (g : G) (y : Option I) : G := y.elim g (K.upd g)

/-- The ghost state after the input decoded at the call `o`. -/
def callGhost (R : Roles X I O C) (K : GContract I G) (g : G) (o : Callout) : G :=
  K.after g (R.callIn o)

/-- The ghost state after the inputs decoded at the call `o` and at its answer `w`. -/
def ansGhost (R : Roles X I O C) (K : GContract I G) (g : G) (o : Callout) (w : HostReply) : G :=
  K.after (callGhost R K g o) (R.answerIn o w)

/-- The ghost state after the inputs of a tag list. -/
def tagGhost (upd : G → I → G) : G → List (Tag X I O C) → G
  | g, [] => g
  | g, .inp x :: ts => tagGhost upd (upd g x) ts
  | g, _ :: ts => tagGhost upd g ts

/-- **The specification of import `i`** (host code `k`) under a ghost contract: the call is
allowed in a store carrying the ghost `g` when `K.pre g` holds of the callout; the answer
carries the ghost moved over the decoded inputs, meets `K.reply`, and its decoded input meets
`K.ans`. -/
def gImportSpec (k : Nat) (i : Import) (memAddr : Option Nat) (R : Roles X I O C)
    (K : GContract I G) : FSpec (Nat × G) where
  pre s args := ∃ g sR, s = gStore g sR ∧ K.pre g (calloutIn i memAddr sR args)
  post s args s' o := ∃ g sR, s = gStore g sR ∧ ∃ r sR', resultOutcome r = o ∧
    s' = gStore (ansGhost R K g (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩) sR' ∧
    K.reply ⟨k, sR, args⟩ ⟨sR', r⟩ ∧
    ∀ x, R.answerIn (calloutIn i memAddr sR args) ⟨r, memOf memAddr sR'⟩ = some x → K.ans x

/-- The specification context of a ghost contract, by import index. -/
def gCtx (m : Module) (memAddr : Option Nat) (R : Roles X I O C) (K : GContract I G) :
    Ctx (Nat × G) := fun k => (m.imports[k]?).map fun i => gImportSpec k i memAddr R K

/-- **The most general environment meeting a ghost contract**: host code `(k, g)` is import
`k`. -/
def gHost (m : Module) (memAddr : Option Nat) (R : Roles X I O C) (K : GContract I G) :
    HostSemantics (Nat × G) :=
  Silmaril.Wasm.Logic.Open.specHost Prod.fst (gCtx m memAddr R K)

/-- The specification of an export address for the ghost invariant `Inv`. -/
def gExportSpec (Inv : G → Store Nat → Prop) (a : Nat) : FSpec (Nat × G) where
  pre s args := ∃ g sR, s = gStore g sR ∧ Inv g sR ∧ InvokeOk sR a args
  post _ _ s' _ := ∀ g sR, s' = gStore g sR → Inv g sR

/-- The postcondition of the instantiation run: if it returns, the ghost invariant holds. -/
def gInstPost (Inv : G → Store Nat → Prop) : Post (Nat × G) :=
  fun s _ o => ∀ vs, o = .normal vs → ∀ g sR, s = gStore g sR → Inv g sR

/-- **The ghost Hoare-logic obligation** of a module under a ghost contract, from the initial
ghost `g₀`. -/
def GMemSat (P : Profile) (m : Module) (memIdx : Nat) (R : Roles X I O C) (K : GContract I G)
    (Inv : G → Store Nat → Prop) (g₀ : G) : Prop :=
  ∀ (mt : CModuleType) (Is : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt Is c₀ →
    (∀ n, Safe P (gHost m c₀.frame.module.mems[memIdx]? R K) (gInstPost Inv) n (gConfig g₀ c₀)) ∧
    ∀ a ∈ Is.addrs, FSpecValid P (gHost m c₀.frame.module.mems[memIdx]? R K) a (gExportSpec Inv a)

end Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost
