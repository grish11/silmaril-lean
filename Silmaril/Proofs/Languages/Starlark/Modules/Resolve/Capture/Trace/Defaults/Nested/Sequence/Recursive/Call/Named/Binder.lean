module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve (PlainKeywordParameter)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value Error allocateTuple allocateDict tupleElements projectCell getCell fromExcept Meaning)

private theorem names_total (parameters : List Parameter) (kwargs : Option Binding) (keywords : Keywords)
    (bound : Bindings × Keywords) : ∃ result, BindsNames parameters kwargs bound keywords result := by
  induction keywords generalizing bound with
  | nil => exact ⟨_, .done bound⟩
  | cons keyword rest ih =>
    obtain ⟨name, value⟩ := keyword
    cases found : parameters.find? (fun p => p.slot.name == name) with
    | none =>
      cases kwargs with
      | none => exact ⟨_, .unknown rfl found⟩
      | some slot =>
        cases previous : List.lookup name bound.2 with
        | some value => exact ⟨_, .repeated rfl found previous⟩
        | none =>
          obtain ⟨result, delivered⟩ := ih (bound.1, bound.2 ++ [(name, value)])
          exact ⟨result, .collect rfl found previous delivered⟩
    | some formal =>
      cases previous : List.lookup formal.slot bound.1 with
      | some value => exact ⟨_, .conflict found previous⟩
      | none =>
        obtain ⟨result, delivered⟩ := ih ((formal.slot, value) :: bound.1, bound.2)
        exact ⟨result, .deliver found previous delivered⟩

theorem binds_total (positional named : List Parameter) (varargs kwargs : Option Binding) (saved : Bindings)
    (actual : Actual) : ∃ result, Binds positional named varargs kwargs saved actual result := by
  by_cases surplus : varargs = none ∧ positional.length < actual.positional.length
  · exact ⟨_, .surplus surplus.1 surplus.2⟩
  · have enough : Fits varargs positional actual := fun absent =>
      Nat.le_of_not_gt (fun overflow => surplus ⟨absent, overflow⟩)
    obtain ⟨result, delivered⟩ := names_total named kwargs actual.keywords ((positional.map Parameter.slot).zip actual.positional, [])
    cases result with
    | error error => exact ⟨_, .rejected enough delivered⟩
    | ok result =>
      obtain ⟨bound, extras⟩ := result
      by_cases complete : missingNames (withDefaults named bound saved) = []
      · exact ⟨_, .assigned enough delivered complete⟩
      · exact ⟨_, .missing enough delivered complete⟩

private theorem delivered_exact (signature : Signature)
    {initial : Bindings × Keywords} {keywords : Keywords} {result : Except Error (Bindings × Keywords)}
    (delivered : BindsNames signature.named signature.kwargs initial keywords result) :
    keywords.foldlM (bindKeyword signature) initial = result := by
  induction delivered with
  | done => rfl
  | unknown absent find => simp [List.foldlM_cons, bindKeyword, find, absent, bind, Except.bind]
  | conflict find previous => simp [List.foldlM_cons, bindKeyword, find, previous, bind, Except.bind]
  | deliver find absent _ ih => simpa [List.foldlM_cons, bindKeyword, find, absent, bind, Except.bind] using ih
  | repeated collector find previous =>
    simp [List.foldlM_cons, bindKeyword, collector, find, previous, bind, Except.bind]
  | collect collector find absent _ ih =>
    simpa [List.foldlM_cons, bindKeyword, collector, find, absent, bind, Except.bind] using ih

private theorem delivered_surplus (parameters : List Parameter) (kwargs : Option Binding)
    {initial : Bindings × Keywords} {keywords : Keywords} {result : Except Error (Bindings × Keywords)}
    (source : BindsNames parameters kwargs initial keywords result) :
    ∀ out, result = .ok out → out.2 = initial.2 ++
      keywords.filter (fun (name, _) => (parameters.find? (fun formal => formal.slot.name == name)).isNone) := by
  induction source with
  | done =>
    intro out same
    cases same
    simp
  | unknown => intro _ impossible; cases impossible
  | conflict => intro _ impossible; cases impossible
  | repeated => intro _ impossible; cases impossible
  | deliver find _ _ ih =>
    intro out same
    simpa [find] using ih out same
  | collect _ find _ _ ih =>
    intro out same
    simpa [find, List.append_assoc] using ih out same

theorem binding_surplus {positional named : List Parameter} {varargs kwargs : Option Binding} {saved : Bindings}
    {actual : Actual} {bound : BoundArguments}
    (source : Binds positional named varargs kwargs saved actual (.ok bound)) :
    bound.surplusKeywords =
      actual.keywords.filter (fun (name, _) => (named.find? (fun formal => formal.slot.name == name)).isNone) := by
  cases source with
  | assigned _ delivered _ => exact delivered_surplus named kwargs delivered _ rfl

theorem binding_exact (signature : Signature)
    {saved : Bindings} {actual : Actual} {result : Except Error BoundArguments}
    (source : Binds signature.positional signature.named signature.varargs signature.kwargs saved actual result) :
    bindArguments signature saved actual = result := by
  have fits (enough : Fits signature.varargs signature.positional actual) :
      (!((actual.positional.drop (signature.positional.map Parameter.slot).length).isEmpty) &&
        signature.varargs.isNone) = false := by
    cases h : signature.varargs with
    | none =>
      have drop : actual.positional.drop (signature.positional.map Parameter.slot).length = [] := by
        simp [List.drop_eq_nil_iff, enough h]
      simp only [drop, List.isEmpty_nil, Bool.not_true, Bool.false_and]
    | some slot => simp only [Option.isNone_some, Bool.and_false]
  cases source with
  | surplus noVarargs tooMany =>
    have nonempty : (actual.positional.drop signature.positional.length).isEmpty = false := by
      cases reached : actual.positional.drop signature.positional.length with
      | nil => exact (Nat.not_le.mpr tooMany (List.drop_eq_nil_iff.mp reached)).elim
      | cons => rfl
    simp only [bindArguments, List.length_map, noVarargs, nonempty, Bool.not_false,
      Option.isNone_none, Bool.and_self, ite_true]
    rfl
  | rejected enough delivered =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature delivered, bind, Except.bind]
  | @missing bound extras enough delivered incomplete =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature delivered, bind, Except.bind]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.named bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.named bound saved)))
      return ⟨savedValues (withDefaults signature.named bound saved),
        actual.positional.drop (signature.positional.map Parameter.slot).length, extras⟩) = _
    cases reached : missingNames (withDefaults signature.named bound saved) with
    | nil => exact (incomplete reached).elim
    | cons => rfl
  | @assigned bound extras enough delivered complete =>
    simp only [bindArguments, fits enough, Bool.false_eq_true, ite_false,
      delivered_exact signature delivered, bind, Except.bind]
    change (show Except Error BoundArguments from do
      if !(missingNames (withDefaults signature.named bound saved)).isEmpty then
        throw (.missingArguments (missingNames (withDefaults signature.named bound saved)))
      return ⟨savedValues (withDefaults signature.named bound saved),
        actual.positional.drop (signature.positional.map Parameter.slot).length, extras⟩) = _
    rw [complete]
    simp only [List.length_map]
    rfl

private def positionalPack (varargs : Option Binding) (bound : BoundArguments) : Meaning Bindings :=
  match varargs with
  | none => pure bound.named
  | some slot => do
    let tuple ← allocateTuple bound.surplusPositional
    pure ((slot, tuple) :: bound.named)

private def keywordPack (kwargs : Option Binding) (extras : Keywords) (assigned : Bindings) : Meaning Bindings :=
  match kwargs with
  | none => pure assigned
  | some slot => do
    let dictionary ← allocateDict (keywordEntries extras)
    pure ((slot, dictionary) :: assigned)

private theorem positional_total (varargs : Option Binding) (caller : State) (bound : BoundArguments) :
    ∃ assigned packed, PacksPositionals varargs caller bound assigned packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      positionalPack varargs bound caller = .ok assigned packed := by
  cases varargs with
  | none =>
    exact ⟨bound.named, caller, .ordinary _ _, ⟨rfl, fun _ _ _ h => h⟩, rfl, rfl⟩
  | some slot =>
    let key := (bound.surplusPositional.mapM fun value => (caller.keyOf value).toOption).map
      (fun parts => .openTuple :: parts.flatten ++ [.closeTuple])
    let packed : State := {caller with heap := caller.heap.push ⟨.tuple bound.surplusPositional key, false⟩}
    have allocated : allocateTuple bound.surplusPositional caller = .ok (.tuple caller.heap.size) packed := rfl
    refine ⟨_, packed, .tuple allocated, ⟨rfl, fun address cell below old => ?_⟩, rfl, rfl⟩
    simp [packed, Array.getElem?_push, Nat.ne_of_lt below, old]

private theorem keywords_total (kwargs : Option Binding) (caller : State) (extras : Keywords) (assigned : Bindings) :
    ∃ bindings packed, PacksKeywords kwargs caller extras assigned bindings packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      keywordPack kwargs extras assigned caller = .ok bindings packed := by
  cases kwargs with
  | none =>
    exact ⟨assigned, caller, .ordinary _ _ _, ⟨rfl, fun _ _ _ h => h⟩, rfl, rfl⟩
  | some slot =>
    let packed : State := {caller with heap := caller.heap.push ⟨.dict (keywordEntries extras), false⟩}
    refine ⟨_, packed, .dict rfl, ⟨rfl, fun address cell below old => ?_⟩, rfl, rfl⟩
    simp [packed, Array.getElem?_push, Nat.ne_of_lt below, old]

theorem packs_total (signature : Signature) (caller : State) (bound : BoundArguments) :
    ∃ assigned packed, Packs signature.varargs signature.kwargs caller bound assigned packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      packArgs signature bound caller = .ok assigned packed := by
  obtain ⟨positional, middle, pos, keptPos, bindingsPos, exactPos⟩ := positional_total signature.varargs caller bound
  obtain ⟨assigned, packed, keywords, keptKeywords, bindingsKeywords, exactKeywords⟩ :=
    keywords_total signature.kwargs middle bound.surplusKeywords positional
  have kept : Body.Keeps caller.heap.size caller packed := by
    refine ⟨keptKeywords.1.trans keptPos.1, fun address cell below old => ?_⟩
    have remains := keptPos.2 address cell below old
    exact keptKeywords.2 address cell (Array.getElem?_eq_some_iff.mp remains).choose remains
  refine ⟨assigned, packed, ⟨positional, middle, pos, keywords⟩, kept, bindingsKeywords.trans bindingsPos, ?_⟩
  cases varargs : signature.varargs with
  | none =>
    simp only [positionalPack, varargs, pure, EStateM.pure] at exactPos
    rcases EStateM.Result.ok.inj exactPos with ⟨rfl, rfl⟩
    simp only [packArgs, varargs, bind, EStateM.bind, pure, EStateM.pure, keywordPack, keywordEntries] at exactKeywords ⊢
    exact exactKeywords
  | some slot =>
    cases allocation : allocateTuple bound.surplusPositional caller with
    | error error residual =>
      simp [positionalPack, varargs, bind, EStateM.bind, allocation] at exactPos
    | ok tuple residual =>
      simp only [positionalPack, varargs, bind, EStateM.bind, allocation, pure, EStateM.pure] at exactPos
      rcases EStateM.Result.ok.inj exactPos with ⟨rfl, rfl⟩
      simp only [packArgs, varargs, bind, EStateM.bind, allocation, pure, EStateM.pure, keywordPack, keywordEntries] at exactKeywords ⊢
      exact exactKeywords

theorem packed_tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) none caller bound assigned packed) :
    assigned = (slot, .tuple caller.heap.size) :: bound.named ∧
      tupleElements caller.heap.size packed = .ok bound.surplusPositional packed := by
  obtain ⟨_, _, positional, keyword⟩ := packing
  cases keyword
  cases positional with
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨rfl, rfl⟩
    exact ⟨rfl, by
      simp [tupleElements, projectCell, getCell, bind, EStateM.bind, pure, EStateM.pure]⟩

theorem packed_empty_key {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) none caller bound assigned packed) (empty : bound.surplusPositional = []) :
    packed.heap[caller.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩ := by
  obtain ⟨_, _, positional, keyword⟩ := packing
  cases keyword
  cases positional with
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨_, rfl⟩
    simp [empty]

private theorem positional_size {varargs : Option Binding} {caller packed : State} {bound : BoundArguments}
    {assigned : Bindings} (positional : PacksPositionals varargs caller bound assigned packed) :
    packed.heap.size = caller.heap.size + varargs.isSome.toNat := by
  cases positional with
  | ordinary => rfl
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨_, rfl⟩
    simp

theorem packed_dictionary {varargs : Option Binding} {slot : Binding} {caller packed : State}
    {bound : BoundArguments} {assigned : Bindings} (packing : Packs varargs (some slot) caller bound assigned packed) :
    assigned.head? = some (slot, .dict (caller.heap.size + varargs.isSome.toNat)) ∧
      packed.heap[caller.heap.size + varargs.isSome.toNat]? =
        some ⟨.dict (keywordEntries bound.surplusKeywords), false⟩ := by
  obtain ⟨_, middle, positional, keyword⟩ := packing
  rw [← positional_size positional]
  cases keyword with
  | dict allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨rfl, rfl⟩
    simp

theorem packed_both {positional keyword : Binding} {caller packed : State} {bound : BoundArguments}
    {assigned : Bindings} (packing : Packs (some positional) (some keyword) caller bound assigned packed) :
    assigned = (keyword, .dict (caller.heap.size + 1)) :: (positional, .tuple caller.heap.size) :: bound.named ∧
      tupleElements caller.heap.size packed = .ok bound.surplusPositional packed ∧
      packed.heap[caller.heap.size + 1]? = some ⟨.dict (keywordEntries bound.surplusKeywords), false⟩ := by
  have dictionary := (packed_dictionary packing).2
  obtain ⟨_, _, pos, kw⟩ := packing
  cases pos with
  | tuple allocated =>
    rcases EStateM.Result.ok.inj allocated with ⟨rfl, rfl⟩
    cases kw with
    | dict inserted =>
      rcases EStateM.Result.ok.inj inserted with ⟨rfl, rfl⟩
      refine ⟨by simp, ?_, dictionary⟩
      simp [tupleElements, projectCell, getCell, bind, EStateM.bind, pure, EStateM.pure, Array.getElem?_push]

theorem prepare_exact {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope) (program : Program) (available : List DeclarationId)
    (id : DeclarationId) (permitted : id ∈ available) (found : program[id]? = some site.declaration)
    {defining state : State} {address : Nat} (record : ClosureAt site id defining state address)
    (actual : Actual) {result : Except Error BoundArguments} (binding : SiteBinding site record.defaults actual result) :
    match result with
    | .error error => prepareExpanded program available actual (.function address) state = .error error state
    | .ok bound => ∃ assigned packed, Packs site.declaration.signature.varargs site.declaration.signature.kwargs state bound assigned packed ∧
        Body.Keeps state.heap.size state packed ∧ packed.bindings = state.bindings ∧
        prepareExpanded program available actual (.function address) state =
          .ok (.closure ⟨id, permitted, site.declaration.body⟩)
            (activate packed site.declaration record.captures assigned) := by
  let saved := site.defaultKeys.zip record.defaults
  have loaded : getClosure address state = .ok ⟨id, record.captures, saved⟩ state := by
    simp [getClosure, projectCell, getCell, bind, EStateM.bind, record.recorded, saved]
    rfl
  have boundExact : bindArguments site.declaration.signature saved actual = result :=
    binding_exact site.declaration.signature binding
  cases result with
  | error error =>
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, boundExact, fromExcept]
    rfl
  | ok bound =>
    obtain ⟨assigned, packed, packing, kept, bindings, exactPack⟩ := packs_total site.declaration.signature state bound
    refine ⟨assigned, packed, packing, kept, bindings, ?_⟩
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true, boundExact, fromExcept,
      pure, EStateM.pure, exactPack]


end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
