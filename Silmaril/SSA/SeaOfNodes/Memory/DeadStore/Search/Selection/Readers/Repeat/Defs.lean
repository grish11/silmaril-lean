module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Defs

/-! # Exhaust the checked straight-line dead-Store selector -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat

open RVSDG (Origin Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- A vertex observed with its original typed scalar operands and without
the memory edge, which is renumbered when a Store is deleted. -/
inductive Operation (args : List ValueSort) where
  | ret {past : List (List ValueSort)} (value : Origin args past .word)
  | load {past : List (List ValueSort)} (address : Origin args past .address)
  | store {past : List (List ValueSort)} (address : Origin args past .address)
      (value : Origin args past .word)

def operations : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → List (Operation args)
  | _, _, .ret _ value => [.ret value]
  | _, _, .load _ address rest => .load address :: operations rest
  | _, _, .store _ address value rest => .store address value :: operations rest

/-- The target keeps operations in their original order with their operands.
The only operation that can be dropped is a Store. -/
inductive DeletesStores : Nat → List (Operation args) → List (Operation args) → Prop where
  | nil : DeletesStores 0 [] []
  | keep {count : Nat} {source target : List (Operation args)} (op : Operation args)
      (rest : DeletesStores count source target) : DeletesStores count (op :: source) (op :: target)
  | drop {count : Nat} {source target : List (Operation args)} {past : List (List ValueSort)}
      (address : Origin args past .address) (value : Origin args past .word)
      (rest : DeletesStores count source target) :
      DeletesStores (count + 1) (.store address value :: source) target

def storeCount {past : List (List ValueSort)} {version : Nat} (body : Body args past version) : Nat :=
  (Selection.storeVersions body).length

structure Result (args : List ValueSort) where
  graph : Graph args
  deleted : Nat

/-- Reselect on the current graph, so each step rebuilds its version and
reader evidence. A refusal ends the pass. -/
def run (input : Tuple (Val cells) args) : Nat → Graph args → Result args
  | 0, graph => ⟨graph, 0⟩
  | fuel + 1, graph =>
    match Readers.rewrite graph input with
    | none => ⟨graph, 0⟩
    | some step =>
      let result := run input fuel step.graph
      ⟨result.graph, result.deleted + 1⟩

/-- The original Store count suffices to exhaust the checked selector. -/
def rewrite (graph : Graph args) (input : Tuple (Val cells) args) : Result args :=
  run input (storeCount graph) graph

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat
