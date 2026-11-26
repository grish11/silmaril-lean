module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.MixedFlat.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection

open Silmaril.Formats.Arrow
open MixedFlat.File.Window

private theorem parsedFields {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {observed : MixedFlat.Observed}
    (read : MixedFlat.readParsed limits fields metadata body = .ok observed) :
    observed.columns.map Prod.fst = fields := by
  unfold MixedFlat.readParsed at read
  cases bound : MixedFlat.bindBatch limits fields metadata body with
  | error => simp [bound, bind, Except.bind] at read
  | ok plan =>
    cases groups : MixedFlat.readGroups limits.view body 0 plan.assignment.groups with
    | error => simp [bound, groups, bind, Except.bind] at read
    | ok columns =>
      simp [bound, groups, bind, Except.bind, pure, Except.pure] at read
      subst observed
      exact plan.readGroups_fields groups

theorem readAt_fields {input : KBytes} {start stop : Nat} (index : Index input start stop)
    {limits : MixedFlat.Limits} {n : Nat} {observed : MixedFlat.Observed}
    (read : index.readAt limits n = .ok (some observed)) :
    observed.columns.map Prod.fst = index.footer.fields := by
  unfold Index.readAt at read
  cases selected : index.footer.blocks[n]? with
  | none => simp [selected, Option.mapM, pure, Except.pure] at read
  | some block =>
    cases record : MixedFlat.File.readRecord limits input index.footer.fields block with
    | error =>
      simp [selected, record, Option.mapM, Except.mapError, Functor.map, Except.map] at read
    | ok result =>
      simp [selected, record, Option.mapM, Except.mapError, Functor.map, Except.map] at read
      subst observed
      obtain ⟨_, _, _, _, _, parsed⟩ := MixedFlat.File.readRecord_witness record
      exact parsedFields parsed

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection
