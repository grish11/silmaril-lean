module

public import Silmaril.Semantics.Region.Simulation.Defs

public section

namespace Silmaril.Semantics.Region.SimulationProofs

variable {Small Full Lab Event SmallStop FullStop : Type*}
variable {small : TransitionSystem Small Lab Event SmallStop}
variable {full : TransitionSystem Full Lab Event FullStop} {support : Lab → Prop}

theorem liftExit (map : Realizes small full) {s out : Small} {trace : List Event}
    (run : FirstExit small support s trace out) : ∀ {initial}, map.relates s initial →
    ∃ final, FirstExit full support initial trace final ∧ map.relates out final := by
  induction run with
  | leave inside edge outside =>
    intro _ related
    obtain ⟨_, step, related'⟩ := map.step related edge
    exact ⟨_, .leave (map.pc related ▸ inside) step (map.pc related' ▸ outside), related'⟩
  | step inside edge _ ih =>
    intro _ related
    obtain ⟨_, step, related'⟩ := map.step related edge
    obtain ⟨_, tail, final⟩ := ih related'
    exact ⟨_, .step (map.pc related ▸ inside) step tail, final⟩

private theorem startsInside {s t : Full} {es : List Event} (run : FirstExit full support s es t) :
    support (full.pc s) := by cases run <;> assumption

private theorem insideStarts {s t : Full} {es : List Event} (run : Inside full support s es t) :
    support (full.pc s) := by cases run <;> assumption

private theorem uniqueExit (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ∀ es next,
    FirstExit full support s es next → es = trace ∧ next = out := by
  induction run with
  | leave _ edge outside =>
    intro _ _ other
    cases other with
    | leave _ edge' _ => exact det.step_unique edge' edge
    | step _ edge' tail =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      exact False.elim (outside (startsInside tail))
  | step _ edge tail ih =>
    intro _ _ other
    cases other with
    | leave _ edge' outside =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      exact False.elim (outside (startsInside tail))
    | step _ edge' tail' =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      obtain ⟨rfl, rfl⟩ := ih _ _ tail'
      exact ⟨rfl, rfl⟩

private theorem accessible (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) :
    Acc (fun t s => support (full.pc s) ∧ support (full.pc t) ∧ ∃ es, full.step s es t) s := by
  induction run with
  | leave _ edge outside =>
    refine Acc.intro _ ?_
    rintro _ ⟨_, inside, _, other⟩
    obtain ⟨_, rfl⟩ := det.step_unique other edge
    exact False.elim (outside inside)
  | step _ edge _ ih =>
    refine Acc.intro _ ?_
    rintro _ ⟨_, _, _, other⟩
    obtain ⟨_, rfl⟩ := det.step_unique other edge
    exact ih

private theorem progress (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ∀ es mid,
    Inside full support s es mid → ∃ tail next, full.step mid tail next := by
  induction run with
  | leave _ edge outside =>
    intro _ _ insideRun
    cases insideRun with
    | refl => exact ⟨_, _, edge⟩
    | step _ other rest =>
      obtain ⟨_, rfl⟩ := det.step_unique other edge
      exact False.elim (outside (insideStarts rest))
  | step _ edge _ ih =>
    intro _ _ insideRun
    cases insideRun with
    | refl => exact ⟨_, _, edge⟩
    | step _ other rest =>
      obtain ⟨_, rfl⟩ := det.step_unique other edge
      exact ih _ _ rest

theorem completes (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ExitsNormally full support s trace out :=
  ⟨run, uniqueExit det run, ⟨accessible det run, fun es mid insideRun => .inr (progress det run es mid insideRun)⟩,
    fun es mid insideRun _ => let ⟨_, _, step⟩ := progress det run es mid insideRun; det.step_no_halt step⟩

theorem liftProperty (map : Realizes small full) (det : Determinate full) {s : Small} {initial : Full}
    (related : map.relates s initial) (settled : ∃ trace out, FirstExit small support s trace out)
    (P : List Event → Small → Prop) (proved : ∀ trace out, FirstExit small support s trace out → P trace out) :
    (∃ trace final, ExitsNormally full support initial trace final) ∧
    ∀ trace final, FirstExit full support initial trace final → ∃ out, map.relates out final ∧ P trace out := by
  obtain ⟨trace, out, run⟩ := settled
  obtain ⟨final, lifted, finalRelated⟩ := liftExit map run related
  have normal := completes det lifted
  refine ⟨⟨trace, final, normal⟩, ?_⟩
  intro es next other
  obtain ⟨rfl, rfl⟩ := normal.unique es next other
  exact ⟨out, finalRelated, proved _ _ run⟩

end Silmaril.Semantics.Region.SimulationProofs
