module

public import Silmaril.Semantics.Page.Trace.Defs
import Silmaril.Semantics.Page.Thms

public section
namespace Silmaril.Proofs.Semantics.Page

open Silmaril.Semantics.Page
open Silmaril.Semantics.ReadWrite

universe u v w y
variable {Id : Type u} {Content : Type v} {Memory : Type w}
variable {trace : Trace Id Content} {page : Id}
variable {initial middle final : Memory}

theorem store_write_iff {store : Store Id Content Memory} {value : Content} :
    store.access.write initial page value = some middle ↔
      store.domain initial page ∧ store.set initial page (.defined value) = middle := by
  cases h : store.lookup initial page <;> simp [Store.access, Store.domain, h]

theorem store_read_iff {store : Store Id Content Memory} {value : Content} :
    store.access.read initial page = some value ↔ store.lookup initial page = .defined value := by
  cases h : store.lookup initial page <;> simp [Store.access, Slot.value, h]

theorem records_run {Result : Type y} {M : Model Id Content Memory} {program : Program Id Content Result}
    {result : Result} (path : Program.Records program trace result)
    (run : trace.Replays M.store.access initial final) :
    Run M program initial (writeEdits trace.writes) (.returned result final) := by
  induction path generalizing initial with
  | pure =>
    change initial = final at run
    cases run
    exact .pure
  | left _ ih => exact .left (ih run)
  | right _ ih => exact .right (ih run)
  | read _ ih => exact .call (.readDefined (store_read_iff.mp run.1)) (ih run.2)
  | write _ ih =>
    obtain ⟨next, step, tail⟩ := run
    obtain ⟨allocated, rfl⟩ := store_write_iff.mp step
    exact .call (.write allocated) (ih tail)

theorem replay_completion [DecidableEq Id] {M : Model Id Content Memory}
    {image : Image Id Content} (run : trace.Replays M.store.access initial final)
    (complete : Completion M initial image) :
    ∃ target, Replay (writeEdits trace.writes) image target ∧ Completion M final target := by
  induction trace generalizing initial image with
  | nil =>
    change initial = final at run
    cases run
    exact ⟨image, .nil, complete⟩
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2 complete
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨allocated, rfl⟩ := store_write_iff.mp step
      have completion := step_completion (M := M)
        (Step.write (value := v) allocated) complete (.cons rfl .nil)
      obtain ⟨target, replay, completed⟩ := ih tail completion
      exact ⟨target, .cons rfl replay, completed⟩

end Silmaril.Proofs.Semantics.Page
