module

import Silmaril.Semantics.Operational.Environment.Finite.Thms
import Silmaril.Semantics.Operational.Projection.Thms
import Cslib.Foundations.Semantics.LTS.Relation
meta import Silmaril.Semantics.Operational.Environment.Finite.Defs
meta import Mathlib.Data.List.AList

/-! # Finite environment observations and run readback -/

namespace Silmaril.Semantics.Operational.Environment.Finite.Examples

private inductive Request (Key Value : Type*) where
  | read (key : Key)
  | write (key : Key) (value : Value)
  | erase (key : Key)

private inductive Action (Key Value : Type*) where
  | loaded (key : Key) (value : Option Value)
  | written (key : Key) (value : Value)
  | erased (key : Key)
  deriving BEq

variable {Key Value : Type*} [DecidableEq Key]

private def perform (rows : AList (fun _ : Key => Value)) :
    Request Key Value → Action Key Value × AList (fun _ : Key => Value)
  | .read key => (.loaded key (rows.lookup key), rows)
  | .write key value => (.written key value, rows.insert key value)
  | .erase key => (.erased key, rows.erase key)

private def presented (Key Value : Type*) [DecidableEq Key] :
    Cslib.LTS (AList (fun _ : Key => Value)) (Request Key Value × Action Key Value) :=
  ⟨fun source action target => perform source action.1 = (action.2, target)⟩

-- Use the functional operations independently of the finite implementation.
private def semantic (Key Value : Type*) [DecidableEq Key] : Cslib.LTS (Environment Key Value) (Action Key Value) :=
  ⟨fun source action target =>
    match action with
    | .loaded key value => value = source key ∧ target = source
    | .written key value => target = Environment.set source key value
    | .erased key => target = Environment.erase source key⟩

private theorem compatible :
    Projection (presented Key Value) (semantic Key Value) view Prod.snd where
  sound {source action target} step := by
    obtain ⟨request, observed⟩ := action
    cases request with
    | read key =>
      change (.loaded key (source.lookup key), source) = (observed, target) at step
      cases step
      exact ⟨rfl, rfl⟩
    | write key value =>
      change (.written key value, source.insert key value) = (observed, target) at step
      cases step
      exact view_insert source key value
    | erase key =>
      change (.erased key, source.erase key) = (observed, target) at step
      cases step
      exact view_erase source key
  readback {source action target} step := by
    cases action with
    | loaded key value =>
      change value = view source key ∧ target = view source at step
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨(.read key, .loaded key (view source key)), source, rfl, rfl, rfl⟩
    | written key value =>
      exact ⟨(.write key value, .written key value), source.insert key value,
        rfl, rfl, (view_insert source key value).trans step.symm⟩
    | erased key =>
      exact ⟨(.erase key, .erased key), source.erase key, rfl, rfl, (view_erase source key).trans step.symm⟩

private def initialRows : AList (fun _ : Nat => Int) :=
  ((∅ : AList (fun _ : Nat => Int)).insert 3 8).insert 1 4

#guard (perform initialRows (.read 1)).1 == .loaded 1 (some 4)
#guard (perform (perform initialRows (.write 1 11)).2 (.read 1)).1 == .loaded 1 (some 11)
#guard (perform (perform initialRows (.erase 3)).2 (.read 3)).1 == .loaded 3 none

-- Reordering the support changes the witness but preserves the entire map.
example : view (encode (view initialRows) [3, 1, 1, 9]) = view initialRows := by
  apply view_encode
  intro key value present
  have listed := view_supported initialRows key value present
  change key ∈ [1, 3] at listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl <;> simp

#guard (encode (view initialRows) [3, 1, 1, 9]).keys == [3, 1]

example (slots : Nat) (env : Environment (Fin slots) Int) :
    view (encode env (List.finRange slots)) = env :=
  view_encode (fun key _ _ => List.mem_finRange key)

private def middle : Environment Nat Int := Environment.set (view initialRows) 1 11
private def finalView : Environment Nat Int := Environment.erase middle 3

example : ∃ action next, (presented Nat Int).Tr initialRows action next ∧
    action.2 = .written 1 11 ∧ view next = middle :=
  (compatible.step_iff initialRows (.written 1 11) middle).mp rfl

private theorem fourSteps :
    (semantic Nat Int).Execution (view initialRows)
      [.written 1 11, .loaded 1 (some 11), .erased 3, .loaded 3 none]
      finalView [view initialRows, middle, middle, finalView, finalView] :=
  .stepL rfl (.stepL ⟨rfl, rfl⟩ (.stepL rfl (.stepL ⟨rfl, rfl⟩ (.refl _))))

example :
    ∃ final actions witnesses, (presented Nat Int).Execution initialRows actions final witnesses ∧
      actions.map Prod.snd = [.written 1 11, .loaded 1 (some 11), .erased 3, .loaded 3 none] ∧
      witnesses.map view = [view initialRows, middle, middle, finalView, finalView] ∧
      view final = finalView :=
  compatible.execution_readback fourSteps rfl

-- Both presented middle states project to 1. The incoming edge lands only
-- at the left state, while the outgoing edge starts at the right state.
private inductive Phase where
  | start | left | right | finish

private inductive Edge : Phase → Bool → Phase → Prop where
  | enter : Edge .start true .left
  | exit : Edge .right false .finish

private def phaseView : Phase → Nat
  | .start => 0
  | .left | .right => 1
  | .finish => 2

private def phases : Cslib.LTS Phase Bool := ⟨Edge⟩

private def endpointImage : Cslib.LTS Nat Bool :=
  ⟨fun s label t => ∃ source target, Edge source label target ∧ phaseView source = s ∧ phaseView target = t⟩

example : endpointImage.MTr 0 [true, false] 2 :=
  .stepL ⟨.start, .left, .enter, rfl, rfl⟩
    (.stepL ⟨.right, .finish, .exit, rfl, rfl⟩ .refl)

example : ¬ ∃ last, phases.MTr .start [true, false] last := by
  rintro ⟨last, run⟩
  cases run with
  | stepL step tail =>
    cases step
    cases tail with
    | stepL next _ => cases next

example : ¬ Projection phases endpointImage phaseView id := by
  intro projection
  have edge : endpointImage.Tr (phaseView .left) false 2 := ⟨.right, .finish, .exit, rfl, rfl⟩
  obtain ⟨_, _, step, _, _⟩ := projection.readback edge
  cases step

end Silmaril.Semantics.Operational.Environment.Finite.Examples
