module

public import Silmaril.Wasm.Game.Accept.Defs
public import Silmaril.Semantics.Accept.Rel.Defs

/-! # Rejection, never-rejection and indexed callouts of modules

**Rejection** is acceptance through a second distinguished import, `reject(…)`. The values a
module *may reject*, `rejected dec … rej m`, are the values passed to `rej` in some run.

The **universal** reading is the complement. `neverRejected dec … rej m` holds the values
that **no** run, against **no** admitted environment, ever passes to `rej`. It is a safety
property, and it holds vacuously: a value the module never handles at all is never
rejected. So `neverRejected` is not acceptance. `acceptedNotRejected` intersects the two: the
values some run accepts and no run rejects.

This is the outcome-quantifier distinction of `Silmaril.Semantics.Accept`: `neverRejects` is
the complement of `rejectsSome`, not of `acceptsSome`. Here `neverRejected` is literally
`Silmaril.Accept.neverRejects` of the runner that sends a value to its rejecting callouts
(`Silmaril.Wasm.Game.Accept.neverRejected_eq`).

**Indexed callouts.** `Calls P Envs memIdx m` records each callout together with its import
*index* `h`: the host code in the specification's instance, which is the import's position.
Distinct imports may share a `(module, name)`, so names alone can conflate them.
`indexed dec` is the `Silmaril.Accept.IndexedLang` of decoded values per import index.
Erasing the index gives acceptance through every import (`eraseSome_indexed`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Formats.Accept

/-! ## Rejection -/

/-- The values a module may reject: those passed to the import `rej` in some run. -/
def rejected {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (rej : String × String) (m : Module) :
    Lang α :=
  accepted dec P Envs memIdx rej m

/-- **Universal non-rejection**: the values no run ever passes to `rej`. -/
def neverRejected {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (rej : String × String) (m : Module) :
    Lang α :=
  (rejected dec P Envs memIdx rej m)ᶜ

/-- Accepted through `acc` by some run, and passed to `rej` by none. -/
def acceptedNotRejected {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (acc rej : String × String)
    (m : Module) : Lang α :=
  accepted dec P Envs memIdx acc m ∩ neverRejected dec P Envs memIdx rej m

/-- The rejecting callouts carrying the value `a`: the runner whose `neverRejects` is
`neverRejected`. -/
def rejectRuns {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (rej : String × String) (m : Module)
    (a : α) : Set Callout :=
  {o | o ∈ Callouts P Envs memIdx m ∧ o.imp = rej ∧ dec o = some a}

/-! ## Indexed callouts -/

/-- The configuration `c` is calling the import of index `h`, observed as `o`. -/
def CalloutAtIdx (m : Module) (memAddr : Option Nat) (c : Config Nat) (h : Nat) (o : Callout) :
    Prop :=
  ∃ (E : Ctx) (fa : Nat), decompose? c.store c.code = some (E, fa, h, o.args) ∧
    (m.imports[h]?).map (fun i => (i.moduleName, i.name)) = some o.imp ∧
    o.mem = (memAddr.bind fun a => c.store.mems[a]?).map MemInst.bytes

/-- **The reachable callouts with their import index.** -/
def Calls (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module) :
    Set (Nat × Callout) :=
  {p | ∃ (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt I c₀ ∧
    ∃ (L : SEnv UImp) (q₀ : L.S), Envs I.store L ∧
    ∃ (b : Bool) (c : Config Nat) (q : L.S), Session P L c₀ q₀ I.addrs b (c, q) ∧
      CalloutAtIdx m c₀.frame.module.mems[memIdx]? c p.1 p.2}

/-- **Decoded values per import index.** -/
def indexed {α : Type} (dec : Callout → Option α) (P : Profile)
    (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module) :
    Silmaril.Accept.IndexedLang (fun _ : Nat => α) :=
  fun i => {a | ∃ o, (i, o) ∈ Calls P Envs memIdx m ∧ dec o = some a}

end Silmaril.Wasm.Game.Accept
