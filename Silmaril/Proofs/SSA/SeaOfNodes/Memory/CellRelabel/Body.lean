module

public import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Proofs

open RVSDG (Locals Origin Port Tuple)

set_option backward.isDefEq.respectTransparency false

variable {cells : Nat} {args : List ValueSort}

theorem read_heap (σ : Permutation cells) (initial : Heap cells) (a : Address cells) :
    (heap σ initial).read (σ a) = initial.read a :=
  congrArg initial (σ.symm_apply_apply a)

theorem write_heap (σ : Permutation cells) (initial : Heap cells) (a : Address cells) (word : Word) :
    (heap σ initial).write (σ a) word = heap σ (initial.write a word) := by
  funext address
  obtain ⟨old, rfl⟩ := σ.surjective address
  calc
    ((heap σ initial).write (σ a) word) (σ old) =
        Function.update (fun x => heap σ initial (σ x)) a word old :=
      Function.update_apply_of_injective (β := fun _ : Address cells => Word) (heap σ initial) σ.injective a word old
    _ = (initial.write a word) old :=
      congrArg (fun h : Heap cells => Function.update h a word old) (funext fun x => read_heap σ initial x)
    _ = heap σ (initial.write a word) (σ old) := (read_heap σ _ old).symm

theorem input_get (σ : Permutation cells) (values : Tuple (Val cells) args)
    {sort : ValueSort} (port : Port args sort) :
    (input σ values).get port = value σ sort (values.get port) := by
  induction port with
  | head => cases values with | cons _ _ => rfl
  | tail _ ih => cases values with | cons _ rest => exact ih rest

private def locals (σ : Permutation cells) : {past : List (List ValueSort)} →
    Locals (Val cells) past → Locals (Val cells) past
  | [], _ => PUnit.unit
  | _ :: _, values => (input σ values.1, locals σ values.2)

private theorem locals_get (σ : Permutation cells) {past : List (List ValueSort)}
    (values : Locals (Val cells) past) (i : Fin past.length) :
    (locals σ values).get i = input σ (values.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih values.2 j) i

private theorem readValue_relabel (σ : Permutation cells) (inputs : Tuple (Val cells) args)
    {past : List (List ValueSort)} (ls : Locals (Val cells) past) {sort : ValueSort}
    (origin : Origin args past sort) :
    readValue origin (input σ inputs) (locals σ ls) = value σ sort (readValue origin inputs ls) := by
  cases origin with
  | arg port => exact input_get σ inputs port
  | output i port =>
    change ((locals σ ls).get i).get port = _
    rw [locals_get, input_get]
    rfl

private theorem denote_body (σ : Permutation cells) (inputs : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {version : Nat} → (body : Body args past version) →
    (ls : Locals (Val cells) past) → (initial : Heap cells) →
    body.denote (input σ inputs) (locals σ ls) (heap σ initial) =
      result σ (body.denote inputs ls initial)
  | _, _, .ret _ origin, ls, initial => by
    rw [Body.denote, Body.denote, readValue_relabel]
    rfl
  | _, _, .load _ address rest, ls, initial => by
    rw [Body.denote, Body.denote, readValue_relabel, show value σ .address _ = σ _ from rfl, read_heap]
    exact denote_body σ inputs rest (.cons (initial.read (readValue address inputs ls)) .nil, ls) initial
  | _, _, .store _ address source rest, ls, initial => by
    rw [Body.denote, Body.denote, readValue_relabel, readValue_relabel]
    change rest.denote (input σ inputs) (locals σ ls)
      ((heap σ initial).write (σ (readValue address inputs ls)) (readValue source inputs ls)) = _
    rw [write_heap]
    exact denote_body σ inputs rest ls _

theorem denote_graph (σ : Permutation cells) (graph : Memory.Graph args)
    (inputs : Tuple (Val cells) args) (initial : Heap cells) :
    graph.denote (input σ inputs) (heap σ initial) = result σ (graph.denote inputs initial) :=
  denote_body σ inputs graph PUnit.unit initial

end Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Proofs
