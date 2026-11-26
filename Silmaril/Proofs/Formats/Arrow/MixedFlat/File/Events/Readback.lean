module

public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Defs
public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Strict.Thms
public import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Window.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.File.Events

private theorem ofObserved_agrees (fields : List MixedFlat.Field) (observed : MixedFlat.Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount) :
    Agrees (schema fields) observed (ofObserved fields observed ordered aligned) := by
  have width : observed.columns.length = fields.length := by
    simpa using congrArg List.length ordered
  refine ⟨rfl, width, fun i => ?_⟩
  have bound : i.val < observed.columns.length := Nat.lt_of_lt_of_eq i.isLt width.symm
  have label := congrArg (fun values : List MixedFlat.Field => values[i.val]?) ordered
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem (show i.val < fields.length from i.isLt), Option.map_some,
    Option.some.injEq] at label
  rw [List.getElem?_eq_getElem bound]
  simp [ofObserved, schema, label]

private theorem drain_exact (limits : MixedFlat.Limits) (input : KBytes)
    (fields : List MixedFlat.Field) (blocks : List FileBlock) (n rows : Nat)
    {events : List (Batch (schema fields))}
    (drained : read.drain limits input fields n rows blocks = .ok events) :
    ∃ observed, blocks.mapM (MixedFlat.File.readRecord limits input fields) = .ok observed ∧
      List.Forall₂ (Agrees (schema fields)) observed events := by
  induction blocks generalizing n rows events with
  | nil =>
    simp only [read.drain, Except.ok.injEq] at drained
    subst events
    exact ⟨[], rfl, .nil⟩
  | cons block rest ih =>
    unfold read.drain at drained
    split at drained
    · contradiction
    · rename_i observed parsed
      cases budget : Body.checkBudget limits.observation fields.length (rows + observed.rowCount) with
      | error =>
        simp [budget, bind, Except.bind, Except.mapError] at drained
      | ok _ =>
        cases remaining : read.drain limits input fields (n + 1) (rows + observed.rowCount) rest with
        | error =>
          simp [budget, remaining, bind, Except.bind, Except.mapError] at drained
        | ok tail =>
          simp [budget, remaining, bind, Except.bind, Except.mapError, pure, Except.pure] at drained
          subst events
          obtain ⟨values, strict, agrees⟩ := ih _ _ remaining
          refine ⟨observed :: values, ?_, .cons (ofObserved_agrees _ _ _ _) agrees⟩
          simp [List.mapM_cons, parsed, strict, bind, Except.bind, pure, Except.pure]

theorem read_exact {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature}
    (success : read limits input = .ok source) :
    ∃ index : MixedFlat.File.Index input,
      MixedFlat.File.readIndex limits.observation.ipc input = .ok index ∧
      source.1 = schema index.footer.fields ∧ source.2.termination = .eos ∧
      ∃ observed, index.footer.blocks.mapM (MixedFlat.File.readRecord limits input index.footer.fields) =
        .ok observed ∧ List.Forall₂ (Agrees source.1) observed source.2.batches := by
  cases opened : MixedFlat.File.readIndex limits.observation.ipc input with
  | error => simp [MixedFlat.File.Events.read, opened, bind, Except.bind, Except.mapError] at success
  | ok index =>
    cases drained : read.drain limits input index.footer.fields 0 0 index.footer.blocks with
    | error => simp [MixedFlat.File.Events.read, opened, drained, bind, Except.bind, Except.mapError] at success
    | ok batches =>
      simp [MixedFlat.File.Events.read, opened, drained, bind, Except.bind, Except.mapError, pure, Except.pure] at success
      subst source
      exact ⟨index, rfl, rfl, rfl, drain_exact _ _ _ _ _ _ drained⟩

private theorem schema_same {limits : Arrow.Limits} {input : KBytes}
    {index : MixedFlat.File.Index input} {window : MixedFlat.File.Window.Index input 0 input.len}
    (strict : MixedFlat.File.readIndex limits input = .ok index)
    (indexed : MixedFlat.File.Window.readIndex limits input 0 input.len = .ok window) :
    schema index.footer.fields = window.projectionSchema := by
  have strictProof := MixedFlat.File.readIndex_exact strict
  have windowProof := MixedFlat.File.Window.readIndex_exact indexed
  have size : index.schemaSize = window.schemaSize :=
    Envelope.metadata.inj (Except.ok.inj (strictProof.2.1.symm.trans windowProof.2.2.1))
  have declarations := strictProof.2.2.1
  simp only [MixedFlat.File.Index.schemaMetadata, size] at declarations
  have original := windowProof.2.2.2.1
  simp only [MixedFlat.File.Window.Index.schemaMetadata, Nat.zero_add] at original
  have fields := Except.ok.inj (declarations.symm.trans original)
  exact congrArg schema fields

private theorem keepAll_batches {signature : Scan.Schema MixedFlat.Field Unit}
    (trace : Trace signature) (projection : Scan.Projection signature) :
    (trace.scan projection (fun _ => some true)).batches = trace.batches.map projection.projectColumns := by
  change trace.batches.map _ = trace.batches.map _
  apply List.map_congr_left
  intro batch _
  have eqRows : projection.scan (fun _ => some true) batch.toRows = projection.project batch.toRows := by
    simp [Scan.Projection.scan, Scan.select]
  change AlignedColumns.ofRows (projection.scan (fun _ => some true) batch.toRows) = _
  rw [eqRows]
  have projectedRows : (projection.projectColumns batch).toRows = projection.project batch.toRows :=
    projection.rowsEquiv_projectColumns batch
  rw [← projectedRows, AlignedColumns.ofRows_toRows]

private theorem cast_agrees {a b : Scan.Schema MixedFlat.Field Unit} (same : a = b)
    (trace : Trace a) (observed : List MixedFlat.Observed)
    (aligned : List.Forall₂ (Agrees a) observed trace.batches) :
    List.Forall₂ (Agrees b) observed (same ▸ trace : Trace b).batches := by
  cases same
  exact aligned

theorem read_projectedAt_scan {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature}
    {window : MixedFlat.File.Window.Index input 0 input.len}
    (success : read limits input = .ok source)
    (indexed : MixedFlat.File.Window.readIndex limits.observation.ipc input 0 input.len = .ok window)
    (projection : Scan.Projection window.projectionSchema) (n : Nat) :
    ∃ same : source.1 = window.projectionSchema,
      let trace : Trace window.projectionSchema := same ▸ source.2
      match (trace.scan projection (fun _ => some true)).batches[n]? with
      | none => window.readProjectedAt limits n projection = .ok none
      | some event => ∃ output, window.readProjectedAt limits n projection = .ok (some output) ∧
          Agrees projection.schema output event := by
  obtain ⟨index, strict, signature, _, observed, drained, aligned⟩ := read_exact success
  let same := signature.trans (schema_same strict indexed)
  refine ⟨same, ?_⟩
  let trace : Trace window.projectionSchema := same ▸ source.2
  change match (trace.scan projection (fun _ => some true)).batches[n]? with
    | none => window.readProjectedAt limits n projection = .ok none
    | some event => ∃ output, window.readProjectedAt limits n projection = .ok (some output) ∧
        Agrees projection.schema output event
  have aligned := cast_agrees same source.2 observed aligned
  have agreement := MixedFlat.File.Window.Index.readProjectedAt_strict strict indexed drained projection n
  rw [keepAll_batches, List.getElem?_map]
  by_cases present : n < observed.length
  · have presentEvent : n < trace.batches.length := aligned.length_eq ▸ present
    rw [List.getElem?_eq_getElem present] at agreement
    rw [List.getElem?_eq_getElem presentEvent, Option.map_some]
    obtain ⟨output, readOutput, count, width, columns⟩ := agreement
    have sameBatch := aligned.get present presentEvent
    refine ⟨output, readOutput, count.trans sameBatch.1, width, fun i => ?_⟩
    rw [columns i]
    exact sameBatch.2.2 (projection.index i)
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt present)] at agreement
    have lengths : observed.length = trace.batches.length := aligned.length_eq
    have absentEvent : trace.batches.length ≤ n := lengths ▸ Nat.le_of_not_gt present
    rw [List.getElem?_eq_none absentEvent]
    exact agreement

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events
