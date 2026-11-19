module

public import Silmaril.Semantics.Function.Examples.Defs
public import Silmaril.Semantics.Function.Semantic.Thms
public import Silmaril.Semantics.Function.Effects.Thms
import Silmaril.Proofs.Semantics.Function.Examples

@[expose] public section
namespace Silmaril.Semantics.Function.Examples

theorem certificate : Correspondence boundary () candidates report := Proofs.certificate

theorem body : boundary.semanticBodies () () () := certificate.body_sound ⟨rfl, rfl⟩

theorem foreign_path : CallPath (mayGraph report.may) (.localFn ()) (.foreign ()) :=
  consecutive_path certificate.may_cover (.single Proofs.actual)

theorem pair_bound : pairEffects.Sound (fun pair => {pair.1.2}) := Proofs.pair_bound

theorem entry_bound : entryEffects.Sound entryBound := Proofs.entry_bound

theorem args_bound : argEffects.Sound (fun args => entryBound (args.1 && args.2)) :=
  Effects.Problem.abstractInput_sound entry_bound (fun _ _ eq => eq.symm ▸ le_rfl)

theorem bounded_not_foreign : ¬ bounded.may ⟨observed.origin, .indirect, .foreign ()⟩ :=
  Proofs.bounded_not_foreign

theorem top_allows_foreign : bounded.topify.may ⟨observed.origin, .indirect, .foreign ()⟩ :=
  ⟨none, ⟨rfl, some {.localFn ()}, rfl, rfl⟩, trivial⟩

theorem wrong_result : ¬ pairEffects.occurs ((false, true), true) true := fun h => Bool.noConfusion h.2

theorem basic_block_exit : Effects.ExitSound system (· = false) (· = false)
    (fun label _ state => label = true ∧ state = true) (fun _ _ _ => True) :=
  (Effects.exitSound_iff ..).mpr ⟨fun _ _ _ _ run => ⟨(Proofs.first_exit run).2.2, (Proofs.first_exit run).2.2⟩,
    fun _ _ _ _ _ _ _ => trivial⟩

end Silmaril.Semantics.Function.Examples
