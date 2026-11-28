module

public import Silmaril.SSA.PEG.Builder

/-! # Checking a coherent renumbering of a PEG table -/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Port)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n n' l l' : Nat}

namespace RawGraph.Check

def portEq : {ps : List (Ty Data)} → {out : Ty Data} →
    (a b : Port ps out) → Decidable (a = b)
  | _, _, .head, .head => isTrue rfl
  | _, _, .head, .tail _ => isFalse (by intro h; cases h)
  | _, _, .tail _, .head => isFalse (by intro h; cases h)
  | _, _, .tail a, .tail b =>
    match portEq a b with
    | isTrue h => isTrue (congrArg Port.tail h)
    | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
termination_by structural _ _ a _ => a

variable [∀ ins out, DecidableEq (P ins out)]

def labelEq {ins : List (Ty Data)} {out : Ty Data}
    (a b : Label P params (Fin l) ins out) : Decidable (a = b) := by
  cases a <;> cases b
  case param.param a b =>
    letI := portEq a b
    if h : a = b then exact isTrue (congrArg Label.param h)
    else exact isFalse (by intro eq; cases eq; exact h rfl)
  case op.op a b =>
    if h : a = b then exact isTrue (h ▸ rfl) else exact isFalse (by
      intro eq
      cases eq
      exact h rfl)
  case phi.phi => exact isTrue rfl
  case theta.theta a b => exact decidable_of_iff (a = b) (by simp)
  case eval.eval a b => exact decidable_of_iff (a = b) (by simp)
  case pass.pass a b => exact decidable_of_iff (a = b) (by simp)
  all_goals exact isFalse (by intro h; cases h)

def rowEq [DecidableEq Data] {out : Ty Data}
    (a b : RawNode P params l out) : Decidable (a = b) := by
  obtain ⟨ins, label, args⟩ := a
  obtain ⟨ins', label', args'⟩ := b
  if hi : ins = ins' then
    subst ins'
    letI := labelEq label label'
    if hl : label = label' then
      if ha : args = args' then exact isTrue (by subst label'; subst args'; rfl)
      else exact isFalse (fun h => ha (congrArg RawNode.args h))
    else exact isFalse (by intro h; cases h; exact hl rfl)
  else exact isFalse (fun h => hi (congrArg RawNode.inputs h))

/-- Exact serialized equality for a numbered table, including loop IDs and parents. -/
def tableEq [DecidableEq Data] (a b : RawGraph P params results n l) : Decidable (a = b) := by
  obtain ⟨⟨forest⟩, sort, node, roots⟩ := a
  obtain ⟨⟨forest'⟩, sort', node', roots'⟩ := b
  if hf : ∀ i, forest i = forest' i then
    have he := funext hf
    subst forest'
    if hs : ∀ i, sort i = sort' i then
      have he := funext hs
      subst sort'
      letI (i : Fin n) := rowEq (node i) (node' i)
      if hn : ∀ i, node i = node' i then
        have he := funext hn
        subst node'
        if hr : roots = roots' then exact isTrue (by subst roots'; rfl)
        else exact isFalse (fun h => hr (congrArg RawGraph.roots h))
      else exact isFalse (by intro h; cases h; exact hn fun _ => rfl)
    else exact isFalse (by intro h; cases h; exact hs fun _ => rfl)
  else exact isFalse (by intro h; cases h; exact hf fun _ => rfl)

end RawGraph.Check

/-- The new graph agrees with the specified renumbering of the old graph,
including types, instruction labels, ordered wires, roots, and parents. -/
structure Graph.ReindexCertificate (old : Graph P params results n l)
    (new : Graph P params results n' l') (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) : Type where
  table : (old.reindex rows loops).toRaw = new.toRaw

/-- Compare the whole table after applying the candidate bijections. -/
def Graph.checkReindex [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (old : Graph P params results n l) (new : Graph P params results n' l')
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    Option (old.ReindexCertificate new rows loops) :=
  letI := RawGraph.Check.tableEq (old.reindex rows loops).toRaw new.toRaw
  if h : (old.reindex rows loops).toRaw = new.toRaw then some ⟨h⟩ else none

/-- Check both inverse laws for a supplied pair of finite identifier maps. -/
def checkFinEquiv (forward : Fin n' → Fin n) (backward : Fin n → Fin n') :
    Option (Fin n' ≃ Fin n) :=
  if left : ∀ i, backward (forward i) = i then
    if right : ∀ j, forward (backward j) = j then
      some ⟨forward, backward, left, right⟩
    else none
  else none

end Silmaril.SSA.PEG
