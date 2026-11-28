module

public import Silmaril.Semantics.Page.Array.Thms
public import Silmaril.Semantics.ReadWrite.Observations.Thms
import Silmaril.Proofs.Semantics.Page.Array.Observations.Laws

/-! Repeated observations on fixed-size page arrays. -/

public section
namespace Silmaril.Semantics.Page

open ReadWrite

universe v
variable {Content : Type v} {n : Nat} {trace : Trace Nat Content}

theorem UndefArray.access_frames :
    (UndefArray.access n Content).Frames (UndefArray.access n Content).read :=
  Proofs.Semantics.Page.Array.Observations.undef_access_frames

theorem UndefArray.access_readsAfterWrite : (UndefArray.access n Content).ReadsAfterWrite :=
  Proofs.Semantics.Page.Array.Observations.undef_access_readsAfterWrite

theorem UndefArray.replays_matchLastWrite {before after : UndefArray n Content}
    (replay : trace.Replays (UndefArray.access n Content) before after) (page : Nat) :
    trace.ReadsMatchLastWrite page :=
  replay.matchLastWrite UndefArray.access_frames UndefArray.access_readsAfterWrite

theorem Array.access_frames : (Array.access n Content).Frames (Array.access n Content).read :=
  Proofs.Semantics.Page.Array.Observations.access_frames

theorem Array.access_readsAfterWrite : (Array.access n Content).ReadsAfterWrite :=
  Proofs.Semantics.Page.Array.Observations.access_readsAfterWrite

theorem Array.replays_matchLastWrite {before after : Array n Content}
    (replay : trace.Replays (Array.access n Content) before after) (page : Nat) :
    trace.ReadsMatchLastWrite page :=
  replay.matchLastWrite Array.access_frames Array.access_readsAfterWrite

end Silmaril.Semantics.Page
