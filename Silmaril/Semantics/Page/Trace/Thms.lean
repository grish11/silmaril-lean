module

public import Silmaril.Semantics.Page.Trace.Defs
public import Silmaril.Semantics.ReadWrite.Thms
import Silmaril.Proofs.Semantics.Page.Trace.Laws

/-! Replay laws for numbered-page stores, programs and completed images. -/

public section
namespace Silmaril.Semantics.Page

open ReadWrite

universe u v w y
variable {Id : Type u} {Content : Type v} {Memory : Type w}
variable {trace : Trace Id Content} {page : Id}
variable {initial middle final : Memory}

theorem Store.access_write_iff {store : Store Id Content Memory} {value : Content} :
    store.access.write initial page value = some middle ↔
      store.domain initial page ∧ store.set initial page (.defined value) = middle :=
  Proofs.Semantics.Page.store_write_iff

theorem Store.access_read_iff {store : Store Id Content Memory} {value : Content} :
    store.access.read initial page = some value ↔ store.lookup initial page = .defined value :=
  Proofs.Semantics.Page.store_read_iff

/-- A page write preserves the full slot at every other address. -/
theorem Store.access_frames (store : Store Id Content Memory) : store.access.Frames store.lookup := by
  intro initial next page value other written different
  obtain ⟨_, rfl⟩ := Store.access_write_iff.mp written
  exact store.lookup_set_other initial page other _ different

theorem Store.access_frames_read (store : Store Id Content Memory) :
    store.access.Frames store.access.read := by
  intro initial next page value other written different
  exact congrArg Slot.value (store.access_frames written different)

theorem Store.replays_use_defined {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final) (used : trace.Uses page) :
    ∃ value, store.lookup initial page = .defined value :=
  let ⟨value, read⟩ := run.use_readable store.access_frames_read used
  ⟨value, Store.access_read_iff.mp read⟩

theorem Program.Records.run {Result : Type y} {M : Model Id Content Memory} {program : Program Id Content Result}
    {result : Result} (path : Program.Records program trace result)
    (run : trace.Replays M.store.access initial final) :
    Run M program initial (writeEdits trace.writes) (.returned result final) :=
  Proofs.Semantics.Page.records_run path run

theorem replays_completion [DecidableEq Id] {M : Model Id Content Memory}
    {image : Image Id Content} (run : trace.Replays M.store.access initial final)
    (complete : Completion M initial image) :
    ∃ target, Replay (writeEdits trace.writes) image target ∧ Completion M final target :=
  Proofs.Semantics.Page.replay_completion run complete

end Silmaril.Semantics.Page
