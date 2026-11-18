module

public import Silmaril.Semantics.Region.Simulation.Defs
public import Silmaril.Semantics.Region.Semantic.Thms
import Silmaril.Proofs.Semantics.Region.Simulation

public section

namespace Silmaril.Semantics.Region

variable {Small Full Lab Event SmallStop FullStop : Type*}
variable {small : TransitionSystem Small Lab Event SmallStop}
variable {full : TransitionSystem Full Lab Event FullStop} {support : Lab → Prop}

theorem Realizes.firstExit (map : Realizes small full) {s out : Small} {trace : List Event}
    (run : FirstExit small support s trace out) {initial} (related : map.relates s initial) :
    ∃ final, FirstExit full support initial trace final ∧ map.relates out final :=
  SimulationProofs.liftExit map run related

theorem FirstExit.completes (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ExitsNormally full support s trace out :=
  SimulationProofs.completes det run

theorem ExitsNormally.not_diverges {s out : Full} {trace : List Event}
    (run : ExitsNormally full support s trace out) : ¬ Diverges full support s :=
  finishes_not_diverges run.finishes

theorem ExitsNormally.not_stuck {s out mid : Full} {trace eventsSoFar : List Event}
    (run : ExitsNormally full support s trace out)
    (inside : Inside full support s eventsSoFar mid) : ¬ Stuck full mid := by
  intro stuck
  rcases run.finishes.2 eventsSoFar mid inside with ⟨stop, halt⟩ | ⟨events, next, step⟩
  · exact stuck.2 stop halt
  · exact stuck.1 events next step

/-- Transfer a property of every simple first exit from a settled entry. The
witness certifies non-vacuity; determinacy makes the property hold of every
full first exit and excludes stuck states, halts and divergence before it. -/
theorem Realizes.liftProperty (map : Realizes small full) (det : Determinate full)
    {s : Small} {initial : Full} (related : map.relates s initial)
    (settled : ∃ trace out, FirstExit small support s trace out)
    (P : List Event → Small → Prop) (proved : ∀ trace out, FirstExit small support s trace out → P trace out) :
    (∃ trace final, ExitsNormally full support initial trace final) ∧
    ∀ trace final, FirstExit full support initial trace final → ∃ out, map.relates out final ∧ P trace out :=
  SimulationProofs.liftProperty map det related settled P proved

end Silmaril.Semantics.Region
