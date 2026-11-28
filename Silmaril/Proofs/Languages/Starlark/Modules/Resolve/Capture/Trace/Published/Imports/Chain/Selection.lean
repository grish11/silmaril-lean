module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)

/-- Actual lookup results carry checked provenance at each returned address. -/
inductive SelectedValues (origin program : Program) (state : State) :
    List ImportBinding → Tracked → List (Binding × Lists.Value) → Tracked → Prop where
  | done (env : Tracked) : SelectedValues origin program state [] env [] env
  | next {item : ImportBinding} {rest : List ImportBinding} {env final : Tracked}
      {callee : Callee} {address : Nat} {entries : List (Binding × Lists.Value)} :
      callee.At origin program state address →
      SelectedValues origin program state rest (track env item.alias (some callee)) entries final →
      SelectedValues origin program state (item :: rest) env ((fileSlot item.alias, .function address) :: entries) final

theorem select_covered {exports : Tracked} {source : Modules.Source} {origin program : Program}
    {state : State} {published : Modules.Published}
    (actual : Publication exports origin program source published state)
    {items : List ImportBinding} {env : Tracked} {selected : Option Tracked}
    (plan : SelectPlan exports source.globals items env selected) (label : String) :
    ∃ out, SelectImports published label items out ∧
      match out, selected with
      | .error _, none => True
      | .ok entries, some final => SelectedValues origin program state items env entries final
      | _, _ => False := by
  induction plan with
  | done env => exact ⟨.ok [], .done, .done env⟩
  | @missing item _ _ absent =>
    have missing : published.exports.lookup item.name = none := by
      cases found : published.exports.lookup item.name with
      | none => rfl
      | some value => exact (absent (actual.1 _ _ found)).elim
    exact ⟨_, .missing missing, trivial⟩
  | @found item _ _ selected callee tracked _ ih =>
    obtain ⟨address, found, record⟩ := actual.2 item.name callee tracked item.publicName
    obtain ⟨out, lookedUp, matched⟩ := ih
    refine ⟨_, .next found lookedUp, ?_⟩
    cases out <;> cases selected
    · exact matched
    · exact matched
    · exact matched
    · exact .next record matched

private theorem select_agrees {published : Modules.Published} {label : String} {items : List ImportBinding}
    {out : Except Modules.Error (List (Binding × Lists.Value))}
    (source : SelectImports published label items out) :
    (items.map ImportBinding.item).mapM (fun item => do
      if !Modules.isPublic item.exportedName then
        throw (.privateImport item.exportedName : Modules.Error)
      let some value := published.exports.lookup item.exportedName |
        throw (.missingExport label item.exportedName : Modules.Error)
      return (fileSlot item.localName, value)) = out := by
  induction source with
  | done => rfl
  | @missing item _ missing =>
    simp [ImportBinding.item, item.publicName, missing, List.mapM_cons, bind, Except.bind, throw,
      throwThe, MonadExceptOf.throw, pure, Except.pure]
  | @next item _ value out found _ ih =>
    simp only [List.map_cons, List.mapM_cons, ImportBinding.item, item.publicName, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at ih ⊢
    rw [ih]
    cases out <;> rfl

theorem group_agrees {published : Modules.Published} {site : ImportSite}
    {out : Except Modules.Error (List (Binding × Lists.Value))}
    (source : SelectImports published site.label site.bindings.reverse out) :
    Modules.importsOf published site.label (site.bindings.map ImportBinding.item) = out := by
  rw [Modules.importsOf, ← List.map_reverse]
  exact select_agrees source

theorem selected_transport {origin program : Program} {state next : State} {items : List ImportBinding}
    {env final : Tracked} {entries : List (Binding × Lists.Value)}
    (selected : SelectedValues origin program state items env entries final)
    (kept : KeepsClosureCells state next) :
    SelectedValues origin program next items env entries final := by
  induction selected with
  | done => exact .done _
  | next record _ ih => exact .next (transport_callable record kept) ih

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
