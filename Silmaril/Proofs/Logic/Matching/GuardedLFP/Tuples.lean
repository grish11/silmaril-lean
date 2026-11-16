module

public import Silmaril.Logic.Matching.GuardedLFP.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem project_pack (M : Model S) (p : Profile S) (args : FirstOrderLFP.Tuple (decode M) p) :
    project M p (pack M p args) = args := by
  funext i
  apply Subtype.ext
  have member : (pack M p args).val ∈ M.base.operation (.pack p) (fun i => (args i).val) :=
    (pack_graph M p args).symm ▸ Set.mem_singleton _
  have hs : {(project M p (pack M p args) i).val} = {(args i).val} :=
    (project_graph M p _ i).symm.trans (M.project_pack p _ _ member i)
  have hm : (project M p (pack M p args) i).val ∈ {(args i).val} :=
    hs ▸ Set.mem_singleton _
  exact hm

theorem pack_project (M : Model S) (p : Profile S) (y : ActiveTuple M.base p) :
    pack M p (project M p y) = y := by
  apply M.tuple_ext p
  intro i
  have member : (pack M p (project M p y)).val ∈
      M.base.operation (.pack p) (fun i => (project M p y i).val) :=
    (pack_graph M p _).symm ▸ Set.mem_singleton _
  exact (M.project_pack p _ _ member i).trans (project_graph M p y i).symm

/-- Derived from actual pack/projection graphs for every admitted raw model. -/
def tupleEquiv (M : Model S) (p : Profile S) : ActiveTuple M.base p ≃ FirstOrderLFP.Tuple (decode M) p where
  toFun := project M p
  invFun := pack M p
  left_inv := pack_project M p
  right_inv := project_pack M p

theorem nullary_active_singleton (M : Model S) (sorts : Fin 0 → S.S) :
    ∃! _y : ActiveTuple M.base ⟨0, sorts⟩, True := by
  refine ⟨pack M ⟨0, sorts⟩ (fun i => i.elim0), trivial, ?_⟩
  intro y _
  apply (tupleEquiv M ⟨0, sorts⟩).injective
  funext i
  exact i.elim0

theorem pack_inactive_empty (M : Model S) (p : Profile S) (args : ∀ i, M.base.carrier (.base (.object (p.sorts i))))
    (i : Fin p.arity) (hi : args i ∉ (baseReduct M.base).operation (.active (p.sorts i)) (fun j => j.elim0)) :
    M.base.operation (.pack p) args = ∅ := by
  apply Set.ext
  intro y
  exact ⟨fun hy => hi ((M.pack_strict p args y hy).1 i), False.elim⟩
end Silmaril.Logic.Matching.GuardedLFP
