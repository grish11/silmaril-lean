module

public import Silmaril.Semantics.Function.Examples.Defs
public import Silmaril.Semantics.Function.Semantic.Thms
public import Silmaril.Semantics.Function.Effects.Thms

public section
namespace Silmaril.Semantics.Function.Examples.Proofs

theorem first_exit {start : Bool} {trace : List Unit} {dest : Bool}
    (run : Region.FirstExit system (· = false) start trace dest) :
    start = false ∧ trace = [()] ∧ dest = true := by
  cases run with
  | leave _ step _ => exact step
  | step _ step rest =>
    obtain ⟨_, _, target⟩ := step
    cases rest <;> simp_all [system]

theorem actual : machine.callStep () observed false true :=
  ⟨rfl, [()], ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem certificate : Correspondence boundary () candidates report := by
  constructor
  · intro name row _
    refine ⟨trivial, rfl, ⟨false, rfl⟩, fun _ eq => eq, fun _ _ => trivial, ?_⟩
    intro start trace dest _ run
    exact (first_exit run).2.2
  · intro name row _ start trace dest _ run
    obtain ⟨rfl, rfl, rfl⟩ := first_exit run
    cases name
    exact Or.inr ⟨observed, false, rfl, actual, [], [()], rfl, .refl rfl, ⟨rfl, rfl, rfl⟩, rfl⟩
  · rintro edge pre post ⟨_, trace, _, rfl, _⟩
    exact ⟨rfl, rfl⟩

theorem pair_bound : pairEffects.Sound (fun pair => {pair.1.2}) := by
  rintro pair event ⟨eq, _⟩
  subst event
  exact le_rfl

theorem inside_stays {start dest : Bool} {trace : List Unit}
    (run : Region.Inside system (· = false) start trace dest) : start = false ∧ dest = false := by
  induction run with
  | refl support => exact ⟨support, support⟩
  | step support _ _ ih => exact ⟨support, ih.2⟩

theorem entry_bound : entryEffects.Sound entryBound := by
  intro state event occurrence
  cases event with
  | inl event =>
    obtain ⟨_, _, _, _, _, rfl, inside, _, _⟩ := occurrence
    obtain rfl := (inside_stays inside).1
    cases event
    exact le_rfl
  | inr stop =>
    obtain ⟨_, _, _, _, inside, halted⟩ := occurrence
    have outside : _ = true := halted
    rw [(inside_stays inside).2] at outside
    cases outside

theorem bounded_not_foreign : ¬ bounded.may ⟨observed.origin, .indirect, .foreign ()⟩ := by
  rintro ⟨_, ⟨_, rfl⟩, admitted⟩
  change Node.foreign () ∈ ({Node.localFn ()} : Set (Node signature)) at admitted
  cases Set.mem_singleton_iff.mp admitted

end Silmaril.Semantics.Function.Examples.Proofs
