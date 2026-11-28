module

import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Semantics.ConcurrentTrace

private abbrev Action := Letter Bool Nat

private def first : Action := .event false 2
private def second : Action := .event true 3
private def barrier : Action := .sync [false, false]
private def emptySync : Action := .sync []

-- Adjacent swaps are available in arbitrary contexts.
example : Equivalent [barrier, first, second, emptySync] [barrier, second, first, emptySync] :=
  Equivalent.swap_in_context (.events (by decide)) [barrier] [emptySync]

-- Saturation admits the swap even when the sequential join places the pair in separate words.
example : [barrier, second] ∈ concat ({[second]} : Set (List Action)) {[barrier]} := by
  apply (mem_saturate _ _).mpr
  exact ⟨[second, barrier], ⟨[second], rfl, [barrier], rfl, rfl⟩,
    Equivalent.swap_in_context (.eventSync (by decide)) [] []⟩

-- Changing order across a participating synchronization changes the trace.
example : ofWord [first, barrier] ≠ ofWord [barrier, first] := by
  intro h
  rcases (swap_eq_iff first barrier).mp h with heq | hind
  · cases heq
  · cases hind with
    | eventSync habsent => exact habsent (by decide)

-- Distinct synchronizations retain global order, including the empty participant list.
example : ofWord [barrier, emptySync] ≠ ofWord [emptySync, barrier] := by
  intro h
  have hs := congrArg (fun x => (syncs x).toList) h
  simp [ofWord_cons, barrier, emptySync, map_mul] at hs

example : (observe false (ofWord [second, barrier, first])).toList = [.sync [false, false], .event 2] := by
  simp [ofWord_cons, second, barrier, first, map_mul, observeLetter]

example : (events false (ofWord [second, barrier, first])).toList = [2] := by
  simp [events, ofWord_cons, second, barrier, first, map_mul, observeLetter, FreeMonoid.lift_eval_of]

-- Thread and event types can both change. Duplicate participants survive the map.
example : mapTrace some (Option.some_injective Bool) (fun _ : Nat => ()) (ofWord [barrier, second]) =
    ofWord [.sync [some false, some false], .event (some true) ()] :=
  mapTrace_ofWord _ _ _ _

-- Even a constant payload map cannot make a noninjective thread map descend globally.
example : ¬ (∀ ⦃x y : Word Bool Nat⦄, Equivalent x y →
    Equivalent (mapWord (fun _ => ()) (fun _ => ()) x) (mapWord (fun _ => ()) (fun _ => ()) y)) := by
  intro h
  have hinj := injective_of_respects (fun _ : Bool => ()) (fun _ : Nat => ()) h
  have hcollapse : false = true := hinj rfl
  cases hcollapse

end Silmaril.Semantics.ConcurrentTrace
