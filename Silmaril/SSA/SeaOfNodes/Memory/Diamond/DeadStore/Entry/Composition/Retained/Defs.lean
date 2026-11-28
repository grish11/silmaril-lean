module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs

/-! Delete one Store on both routes while retaining an ordered entry chain. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

open RVSDG (Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)
open Discovery.MemRef.CF (lowerDiamond)

variable {args : List ValueSort} {cells : Nat}

/-- Read the original argument-addressed Stores, in table order, and the
argument returned by the entry. -/
def stores : {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version →
    Option (List (PrefixStore args) × Port args .word)
  | _, _, .ret _ (.arg word) => some ([], word)
  | _, _, .store _ (.arg address) (.arg value) rest =>
    (stores rest).map fun (tail, word) => (⟨address, value⟩ :: tail, word)
  | _, _, _ => none

/-- Emit a native entry table with a consecutive memory-version chain. -/
def storeTable (word : Port args .word) : (version : Nat) → List (PrefixStore args) → Memory.Body args [] version
  | version, [] => .ret (.latest version) (.arg word)
  | version, store :: rest =>
    .store (.latest version) (.arg store.address) (.arg store.value) (storeTable word (version + 1) rest)

structure Edit (args : List ValueSort) where
  retained : Memory.Graph args
  routes : Discovery.Result args

/-- The nominated version is one-based in the residual entry. Its cell
must differ from each later Store's cell. The retained prefix is unchanged. -/
def rewrite (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Option (Edit args) :=
  match version with
  | 0 => none
  | index + 1 => do
    let (chain, word) ← stores entry
    let selected ← chain[index]?
    let retained := chain.eraseIdx index
    let facts : Certificate args := ⟨selected.address, (chain.drop (index + 1)).map PrefixStore.address⟩
    if facts.check input then
      (Discovery.rewrite ⟨selected, graph⟩ input).map (Edit.mk (storeTable word 0 retained))
    else none

/-- Run the entry-local pass, then try the nominated deletion on the
residual table. Refusal keeps the entry-local result. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Composition.Result cells args :=
  let repeated := Entry.lowerRepeated graph entry input
  match rewrite graph repeated.entry version input with
  | none => ⟨repeated.deleted, false, repeated.programs⟩
  | some edit => ⟨repeated.deleted, true, { repeated.programs with
      optimized := lowerDiamond cells edit.routes.graph (some edit.retained) }⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained
