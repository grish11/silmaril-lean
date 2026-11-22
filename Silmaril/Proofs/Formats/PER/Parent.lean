module

public import Silmaril.Formats.PER.Parent.Defs

public section

namespace Silmaril.Proofs.Formats.PERParent

open Silmaril.Formats PER Parent

variable {Key : Type} {parent : Key → Option Key} {mode : Convention}

theorem no_step {key child : Key} (terminal : Terminal mode parent key) (edge : Step parent key child) : False := by
  cases mode
  · exact edge.2 (Option.some.inj (terminal.symm.trans edge.1))
  · have impossible : none = some child := terminal.symm.trans edge.1
    cases impossible

theorem reaches_unique {key first second : Key} (left : Reaches mode parent key first)
    (right : Reaches mode parent key second) : first = second := by
  induction left generalizing second with
  | stop terminal =>
    cases right with
    | stop => rfl
    | next edge _ => exact (no_step terminal edge).elim
  | next edge _ ih =>
    cases right with
    | stop terminal => exact (no_step terminal edge).elim
    | next otherEdge later =>
      obtain rfl := Option.some.inj (edge.1.symm.trans otherEdge.1)
      exact ih later

theorem reaches_terminal {key root : Key} (path : Reaches mode parent key root) : Terminal mode parent root := by
  induction path with
  | stop terminal => exact terminal
  | next _ _ ih => exact ih

theorem fixed_cover (forest : FixedForest parent) (key : Key) (known : (parent key).isSome) :
    ∃ root, Roots .fixedPoint parent key root := by
  suffices present : ∃ root, Reaches .fixedPoint parent key root by
    obtain ⟨root, path⟩ := present
    exact ⟨root, known, path⟩
  induction key using forest.terminates.induction with
  | h key ih =>
    obtain ⟨next, edge⟩ := Option.isSome_iff_exists.mp known
    by_cases same : key = next
    · exact ⟨key, .stop (edge.trans (congrArg some same.symm))⟩
    · obtain ⟨root, path⟩ := ih next ⟨edge, same⟩ (forest.knownTarget edge)
      exact ⟨root, .next ⟨edge, same⟩ path⟩

theorem missing_cover (forest : MissingForest parent) (key : Key) (known : (parent key).isSome) :
    ∃ root, Roots .terminalMissing parent key root := by
  have reaches (start : Key) : ∃ root, Reaches .terminalMissing parent start root := by
    induction start using forest.terminates.induction with
    | h start ih =>
      cases edge : parent start with
      | none => exact ⟨start, .stop edge⟩
      | some next =>
        have strict : Step parent start next := ⟨edge, fun same => forest.noFixed start (edge.trans (congrArg some same.symm))⟩
        obtain ⟨root, path⟩ := ih next strict
        exact ⟨root, .next strict path⟩
  obtain ⟨root, path⟩ := reaches key
  exact ⟨root, known, path⟩

theorem flat_roots (labels : Key → Option Key) (rooted : Rooted labels) (key root : Key) :
    Roots .fixedPoint labels key root ↔ labels key = some root := by
  constructor
  · intro evidence
    cases evidence.2 with
    | stop terminal => exact terminal
    | next edge path =>
      have same := reaches_unique (.stop (mode := .fixedPoint) (rooted edge.1)) path
      exact same ▸ edge.1
  · intro hit
    refine ⟨Option.isSome_iff_exists.mpr ⟨root, hit⟩, ?_⟩
    by_cases same : key = root
    · subst key; exact .stop hit
    · exact .next ⟨hit, same⟩ (.stop (rooted hit))

end Silmaril.Proofs.Formats.PERParent
