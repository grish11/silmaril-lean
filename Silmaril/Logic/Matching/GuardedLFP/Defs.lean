module

public import Silmaril.Logic.Matching.GuardedFOL
public import Silmaril.Logic.FirstOrderLFP.Thms
public import Silmaril.Logic.Matching.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples
abbrev Profile := FirstOrderLFP.Profile

inductive MatchingSort (S : FOL.Signature) where
  | base : GuardedFOL.MatchingSort S → MatchingSort S
  | tuple : Profile S → MatchingSort S

inductive Operation (S : FOL.Signature) : (n : Nat) → (Fin n → MatchingSort S) → MatchingSort S → Type where
  | base {n inputs output} (op : GuardedFOL.Operation S n inputs output) :
      Operation S n (MatchingSort.base ∘ inputs) (.base output)
  | pack (p : Profile S) : Operation S p.arity (fun i => .base (.object (p.sorts i))) (.tuple p)
  | project (p : Profile S) (i : Fin p.arity) :
      Operation S 1 (fun _ => .tuple p) (.base (.object (p.sorts i)))
  | active (p : Profile S) : Operation S 0 (fun _ => .base .truth) (.tuple p)
  | defined (p : Profile S) : Operation S 1 (fun _ => .tuple p) (.base .truth)
  | liftTruth (p : Profile S) : Operation S 1 (fun _ => .base .truth) (.tuple p)

abbrev signature (S : FOL.Signature) : SortMaps.Signature := ⟨MatchingSort S, ⟨Operation S⟩⟩

abbrev baseSignature (S : FOL.Signature) : GuardedFOL.signature S ⟶ signature S where
  sorts := MatchingSort.base
  operations op := .base op

abbrev baseReduct {S : FOL.Signature} (M : FirstOrder.Model (signature S).symbols) :
    FirstOrder.Model (GuardedFOL.signature S).symbols where
  carrier s := M.carrier (.base s)
  nonempty s := M.nonempty (.base s)
  operation op args := M.operation (.base op) args

theorem baseReduct_eq {S : FOL.Signature} (M : FirstOrder.Model (signature S).symbols) :
    baseReduct M = SortMaps.Hom.reduct (baseSignature S) M := rfl
abbrev ActiveObject {S : FOL.Signature} (M : FirstOrder.Model (signature S).symbols) := GuardedFOL.Active (baseReduct M)
abbrev ActiveTuple {S : FOL.Signature} (M : FirstOrder.Model (signature S).symbols) (p : Profile S) :=
  {x : M.carrier (.tuple p) // x ∈ M.operation (.active p) (fun i => i.elim0)}

/-- Only native operation-graph conditions, including strict packing and two
structural inverse laws; no formula denotation or fixed-point result is assumed. -/
structure Model (S : FOL.Signature) where
  base : FirstOrder.Model (signature S).symbols
  function : ∀ {n inputs output} (op : S.Op n inputs output) (args : ∀ i, ActiveObject base (inputs i)),
    ∃ y : ActiveObject base output, base.operation (.base (.function op)) (fun i => (args i).val) = {y.val}
  relation : ∀ {n inputs} (r : S.Rel n inputs) args,
    base.operation (.base (.relation r)) args = ∅ ∨ base.operation (.base (.relation r)) args = Set.univ
  objectDefined : ∀ s args, base.operation (.base (.defined s)) args = Set.univ
  truth : ∀ args, base.operation (.base .truth) args = Set.univ
  pack_total : ∀ (p : Profile S) (args : ∀ i : Fin p.arity, ActiveObject base (p.sorts i)),
    ∃ y : ActiveTuple base p, base.operation (.pack p) (fun i => (args i).val) = {y.val}
  pack_strict : ∀ p args y, y ∈ base.operation (.pack p) args →
    (∀ i, args i ∈ (baseReduct base).operation (.active (p.sorts i)) (fun j => j.elim0)) ∧
      y ∈ base.operation (.active p) (fun i => i.elim0)
  project_total : ∀ (p : Profile S) (y : ActiveTuple base p) i,
    ∃ x : ActiveObject base (p.sorts i), base.operation (.project p i) (fun _ => y.val) = {x.val}
  project_pack : ∀ p args y, y ∈ base.operation (.pack p) args →
    ∀ i, base.operation (.project p i) (fun _ => y) = {args i}
  tuple_ext : ∀ (p : Profile S) (x y : ActiveTuple base p),
    (∀ i, base.operation (.project p i) (fun _ => x.val) = base.operation (.project p i) (fun _ => y.val)) → x = y
  tupleDefined : ∀ p args, base.operation (.defined p) args = Set.univ
  truthLift : ∀ p args, base.operation (.liftTruth p) args = Set.univ

abbrev guardedModel {S : FOL.Signature} (M : Model S) : GuardedFOL.Model S where
  base := baseReduct M.base
  function := M.function
  relation := M.relation
  definedness := M.objectDefined
  truth := M.truth
abbrev decode {S : FOL.Signature} (M : Model S) : FirstOrderLFP.Model S := ⟨GuardedFOL.decode (guardedModel M)⟩

def pack {S : FOL.Signature} (M : Model S) (p : Profile S)
    (args : FirstOrderLFP.Tuple (decode M) p) : ActiveTuple M.base p := Classical.choose (M.pack_total p args)
def project {S : FOL.Signature} (M : Model S) (p : Profile S)
    (y : ActiveTuple M.base p) (i : Fin p.arity) : ActiveObject M.base (p.sorts i) :=
  Classical.choose (M.project_total p y i)

theorem pack_graph {S : FOL.Signature} (M : Model S) (p : Profile S) (args : FirstOrderLFP.Tuple (decode M) p) :
    M.base.operation (.pack p) (fun i => (args i).val) = {(pack M p args).val} := Classical.choose_spec (M.pack_total p args)
theorem project_graph {S : FOL.Signature} (M : Model S) (p : Profile S) (y : ActiveTuple M.base p) (i : Fin p.arity) :
    M.base.operation (.project p i) (fun _ => y.val) = {(project M p y i).val} := Classical.choose_spec (M.project_total p y i)
end Silmaril.Logic.Matching.GuardedLFP
