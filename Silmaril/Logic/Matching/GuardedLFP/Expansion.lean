module

public import Silmaril.Logic.Matching.GuardedLFP.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples

abbrev SourceTuple {S : FOL.Signature} (M : FOL.Structure S) (p : Profile S) := ∀ i, M.carrier (p.sorts i)
abbrev paddedCarrier {S : FOL.Signature} (M : FOL.Structure S) : MatchingSort S → Type
  | .base s => GuardedFOL.paddedCarrier M s
  | .tuple p => Option (SourceTuple M p)

abbrev rawExpansion {S : FOL.Signature} (M : FOL.Structure S) : FirstOrder.Model (signature S).symbols where
  carrier := paddedCarrier M
  nonempty s := match s with
    | .base s => (GuardedFOL.rawExpansion M).nonempty s
    | .tuple _ => ⟨none⟩
  operation op args := match op with
    | .base o => (GuardedFOL.rawExpansion M).operation o args
    | .pack p => {y | ∃ values : SourceTuple M p, (∀ i, args i = some (values i)) ∧ y = some values}
    | .project p i => {y | ∃ values : SourceTuple M p, args 0 = some values ∧ y = some (values i)}
    | .active _ => Set.range some
    | .defined _ => Set.univ
    | .liftTruth _ => Set.univ

def unpadTuple {S : FOL.Signature} {M : FOL.Structure S} {p : Profile S}
    (x : ActiveTuple (rawExpansion M) p) : SourceTuple M p := Classical.choose x.property

theorem unpadTuple_spec {S : FOL.Signature} {M : FOL.Structure S} {p : Profile S}
    (x : ActiveTuple (rawExpansion M) p) : some (unpadTuple x) = x.val := Classical.choose_spec x.property

theorem raw_project_graph {S : FOL.Signature} (M : FOL.Structure S) (p : Profile S)
    (x : ActiveTuple (rawExpansion M) p) (i : Fin p.arity) :
    (rawExpansion M).operation (.project p i) (fun _ => x.val) = {some (unpadTuple x i)} := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨other, ho, hy⟩
    have same : other = unpadTuple x := Option.some.inj (ho.symm.trans (unpadTuple_spec x).symm)
    exact hy.trans (congrArg (fun t => some (t i)) same)
  · intro hy
    exact ⟨unpadTuple x, (unpadTuple_spec x).symm, hy⟩

/-- Canonical padded object/tuple carriers, with every graph law proved directly. -/
abbrev expand {S : FOL.Signature} (M : FOL.Structure S) : Model S where
  base := rawExpansion M
  function := (GuardedFOL.expand M).function
  relation := (GuardedFOL.expand M).relation
  objectDefined := (GuardedFOL.expand M).definedness
  truth := (GuardedFOL.expand M).truth
  pack_total p args := by
    let values := fun i => GuardedFOL.unpad (args i)
    refine ⟨⟨some values, ⟨values, rfl⟩⟩, ?_⟩
    apply Set.ext
    intro y
    constructor
    · rintro ⟨other, ho, rfl⟩
      have same : other = values := funext fun i => Option.some.inj ((ho i).symm.trans (GuardedFOL.unpad_spec (args i)).symm)
      exact congrArg some same
    · intro hy
      exact ⟨values, fun i => (GuardedFOL.unpad_spec (args i)).symm, hy⟩
  pack_strict p args y h := by
    rcases h with ⟨values, hv, rfl⟩
    exact ⟨fun i => ⟨values i, (hv i).symm⟩, ⟨values, rfl⟩⟩
  project_total p y i :=
    ⟨⟨some (unpadTuple y i), ⟨unpadTuple y i, rfl⟩⟩, raw_project_graph M p y i⟩
  project_pack p args y h := by
    rcases h with ⟨values, hv, rfl⟩
    intro i
    apply Set.ext
    intro result
    constructor
    · rintro ⟨other, ho, hr⟩
      have same : other = values := (Option.some.inj ho).symm
      exact hr.trans ((congrArg (fun t => some (t i)) same).trans (hv i).symm)
    · intro hr
      exact ⟨values, rfl, hr.trans (hv i)⟩
  tuple_ext p x y h := by
    have same : unpadTuple x = unpadTuple y := by
      funext i
      have hs : ({some (unpadTuple x i)} : Set (Option (M.carrier (p.sorts i)))) = {some (unpadTuple y i)} :=
        (raw_project_graph M p x i).symm.trans ((h i).trans (raw_project_graph M p y i))
      have hm : some (unpadTuple x i) ∈ ({some (unpadTuple y i)} : Set (Option (M.carrier (p.sorts i)))) :=
        hs ▸ Set.mem_singleton _
      exact Option.some.inj hm
    exact Subtype.ext ((unpadTuple_spec x).symm.trans ((congrArg some same).trans (unpadTuple_spec y)))
  tupleDefined _ _ := rfl
  truthLift _ _ := rfl
end Silmaril.Logic.Matching.GuardedLFP
