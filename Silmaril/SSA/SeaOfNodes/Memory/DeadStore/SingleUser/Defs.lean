module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs

/-! Check the direct single-user Store bypass on the ordered memory graph. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser

open RVSDG (Locals Port Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {live cells : Nat}

/-- Each list entry records one use occurrence. A Store user is identified
by the version it publishes. Return exports its operand heap. -/
inductive User where
  | load
  | store (published : Nat)
  | ret
  deriving DecidableEq

/-- Read the actual memory operands. Keep every occurrence, including
multiple Loads that use the same producer. -/
def usersOf (producer : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Body args past live → List User
  | _, _, .ret memory _ => if memory.producer.val = producer then [.ret] else []
  | _, _, .load memory _ rest =>
    if memory.producer.val = producer then .load :: usersOf producer rest else usersOf producer rest
  | _, live, .store memory _ _ rest =>
    if memory.producer.val = producer then .store (live + 1) :: usersOf producer rest else usersOf producer rest

/-- The designated Store is followed directly by a Store on the same
original typed pointer. Store versions are one-based. -/
def adjacentAddress (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Body args past live → Option (Port args .address)
  | _, _, .ret _ _ => none
  | _, _, .load _ _ rest => adjacentAddress version rest
  | _, live, .store _ address _ rest =>
    if live + 1 = version then
      match address, rest with
      | .arg earlier, .store _ (.arg later) _ _ =>
        if earlier.index = later.index then some earlier else none
      | _, _ => none
    else adjacentAddress version rest

/-- The overwriting Store must be the sole user of the actual produced
memory version. Replay the existing rewrite with no reader obligations. -/
def rewrite (graph : Graph args) (version : Nat) : Option (Graph args) := do
  if usersOf version graph = [.store (version + 1)] then
    let address ← adjacentAddress version graph
    DeadStore.rewriteWith graph ⟨version, version + 1⟩ ⟨address, []⟩
  else none

/-- Cut the table at a zero-based Load occurrence and return that Load's
word. Stores and preceding Loads keep their original operands. -/
def throughLoad :
    {past : List (List ValueSort)} → {live : Nat} →
      Body args past live → Nat → Option (Body args past live)
  | _, _, .ret _ _, _ => none
  | _, _, .store memory address word rest, index =>
    (throughLoad rest index).map (.store memory address word)
  | _, _, .load memory address _, 0 => some (.load memory address (.ret memory (.output 0 .head)))
  | _, _, .load memory address rest, index + 1 =>
    (throughLoad rest index).map (.load memory address)

/-- Observe the selected Load using the native denotation of its prefix. -/
def readAt (body : Body args past live) (index : Nat) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (initial : Heap cells) : Option Word :=
  (throughLoad body index).map fun selected => (selected.denote input locals initial).1

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser
