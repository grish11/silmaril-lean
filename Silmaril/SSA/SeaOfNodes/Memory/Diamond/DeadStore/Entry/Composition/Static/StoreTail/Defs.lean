module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Defs

/-! Retain one certified disjoint Store and optional Loads after a nominated entry Store. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail

open RVSDG (Tuple)
open Discovery.MemRef.CF (lowerDiamond)
open Memory.Forwarding.Disjoint (Certificate)
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}

/-- The retained Store takes its original scalar operand. Its address
and every later reader must be certified disjoint from the nomination. -/
def checkTail (facts : Certificate args) (store : PrefixStore args) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool
  | _, _, .store _ (.arg writer) _ rest =>
    facts.matches (past := []) (.arg store.address) &&
      ((!facts.matches (past := []) (.arg writer) && facts.covers (past := []) (.arg writer)) &&
        match rest with
        | .ret _ _ => true
        | _ => Final.LoadTail.checkTail facts store rest)
  | _, _, _ => false

def cut (facts : Certificate args) (version : Nat) (entry : Memory.Graph args) :
    Option (PrefixStore args × Memory.Graph args) :=
  Final.cutWith (checkTail facts) version entry

def emit (cells : Nat) (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (facts : Certificate args) : Option (Artifacts cells args) := do
  let (store, retained) ← cut facts version entry
  let edited ← Static.rewrite ⟨store, graph⟩
  some ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩

/-- The one-based nomination is in the table produced by entry discovery.
Validate the supplied facts at this invocation before trying the route cut. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (facts : Certificate args) :
    Except InvocationError (Final.LoadTail.Result cells args) := do
  let stage ← Inference.lower graph entry input
  let routes := if facts.check input then emit cells graph stage.entry version facts else none
  pure ⟨stage, routes⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail
