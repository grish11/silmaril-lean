module

public import Silmaril.Logic.Matching.GuardedLFP
public import Silmaril.Logic.FirstOrderLFP.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

abbrev sortless : FOL.Signature where
  S := Empty
  Op := fun _ _ _ => Empty
  Rel := fun _ _ => Empty

abbrev noSorts : FirstOrderLFP.Model sortless := ⟨{
  carrier := fun s => s.elim
  op := fun o => o.elim
  rel := fun r => r.elim }⟩
abbrev noContext : Fin 0 → sortless.S := Fin.elim0
abbrev nullary : Profile sortless := ⟨0, noContext⟩
abbrev nullaryProfiles : Fin 1 → Profile sortless := fun _ => nullary
abbrev nullaryBody : FirstOrderLFP.Formula sortless nullaryProfiles noContext := .base .tt
abbrev nullaryFixed : FirstOrderLFP.Formula sortless (nullaryProfiles ∘ Fin.succ) noContext :=
  .lfp rfl rfl nullaryBody (fun i => i.elim0)

theorem no_sorts_nullary_native :
    () ∈ (formula nullaryFixed).denote (expand noSorts.toStructure).base
      (fun i => i.elim0) (fun i => i.elim0) := by
  have hv : (fun i => some ((fun j => j.elim0 : FirstOrderLFP.ObjEnv noSorts noContext) i)) =
      (fun i => i.elim0) := funext fun i => i.elim0
  rw [← hv]
  apply (expanded_formula_denote noSorts nullaryFixed (fun i => i.elim0) ()).mpr
  apply (FirstOrderLFP.Formula.denote_lfp noSorts (P' := nullaryProfiles) (Γ := noContext)
    (Δ := noContext) rfl rfl nullaryBody (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)).mpr
  rw [FirstOrderLFP.lfpSet_unfold]
  intro θ hθ
  trivial

theorem nullary_mu_padding_excluded :
    none ∉ (FixedPoint.Pattern.mu (tupleBody (P' := nullaryProfiles) (Γ := noContext)
      rfl rfl (formula nullaryBody))).denote (expand noSorts.toStructure).base
        (fun i => i.elim0) (fun i => i.elim0) := by
  intro h
  let v : FirstOrderLFP.ObjEnv (decode (expand noSorts.toStructure)) noContext := fun i => i.elim0
  have hv : (fun i => i.elim0) = (fun i => (v i).val) := funext fun i => i.elim0
  rw [hv] at h
  have ha : none ∈ (expand noSorts.toStructure).base.operation (.active nullary) (fun i => i.elim0) :=
    native_lfp_active (expand noSorts.toStructure) (P' := nullaryProfiles) (Γ := noContext)
      (Δ := noContext) rfl rfl nullaryBody (formula_denote (expand noSorts.toStructure) nullaryBody)
        v (fun i => i.elim0) h
  rcases ha with ⟨x, hx⟩
  cases hx

theorem nullary_active_despite_empty_objects :
    ∃! _y : ActiveTuple (expand (FirstOrderLFP.Reachability.model Empty (fun _ _ => False)).toStructure).base
      ⟨0, FirstOrderLFP.Reachability.context 0⟩, True :=
  nullary_active_singleton _ _

theorem empty_positive_tuple :
    ¬ Nonempty (ActiveTuple (expand (FirstOrderLFP.Reachability.model Empty (fun _ _ => False)).toStructure).base
      ⟨1, FirstOrderLFP.Reachability.context 1⟩) := by
  rintro ⟨y⟩
  exact (unpadTuple y 0).elim

theorem strict_inactive_pack :
    (expand (FirstOrderLFP.Reachability.model Empty (fun _ _ => False)).toStructure).base.operation
      (.pack ⟨1, FirstOrderLFP.Reachability.context 1⟩) (fun _ => none) = ∅ := by
  apply pack_inactive_empty _ _ _ 0
  rintro ⟨x, hx⟩
  cases hx

/-- A raw set may contain only padding; it does not make the nullary predicate true. -/
theorem inactive_free_set_rejected :
    () ∉ (formula (FirstOrderLFP.Formula.pred (P := nullaryProfiles) (Γ := noContext)
      0 (fun i => i.elim0))).denote (expand noSorts.toStructure).base
        (fun i => i.elim0) (fun _ => {none}) := by
  rintro ⟨truthArgs, hargs, _⟩
  rcases (hargs 0).1 with ⟨packArgs, _, values, _, hvalue⟩
  have hn : truthArgs 0 = none := (hargs 0).2
  have impossible := hn.symm.trans hvalue
  cases impossible

abbrev finiteModel := FirstOrderLFP.Reachability.model (Fin 3) FirstOrderLFP.Examples.cycleEdge

/-- Changing the captured target changes actual native translated truth. -/
theorem captured_parameter_native :
    () ∈ (formula FirstOrderLFP.Reachability.reaches).denote (expand finiteModel.toStructure).base
      (fun i => some (![0, 0] i)) (fun i => i.elim0) ∧
    () ∉ (formula FirstOrderLFP.Reachability.reaches).denote (expand finiteModel.toStructure).base
      (fun i => some (![0, 2] i)) (fun i => i.elim0) := by
  constructor
  · exact (expanded_formula_denote finiteModel FirstOrderLFP.Reachability.reaches ![0, 0] ()).mpr
      FirstOrderLFP.Examples.parameter_matters.1
  · intro h
    exact FirstOrderLFP.Examples.parameter_matters.2
      ((expanded_formula_denote finiteModel FirstOrderLFP.Reachability.reaches ![0, 2] ()).mp h)

abbrev oneWay : Bool → Bool → Prop := fun a b => a = false ∧ b = true
abbrev orderModel := FirstOrderLFP.Reachability.model Bool oneWay

theorem forward_order_native :
    () ∈ (formula FirstOrderLFP.Reachability.transitive).denote (expand orderModel.toStructure).base
      (fun i => some (![false, true] i)) (fun i => i.elim0) := by
  apply (expanded_formula_denote orderModel FirstOrderLFP.Reachability.transitive ![false, true] ()).mpr
  apply (FirstOrderLFP.Reachability.transitive_finite_path oneWay ![false, true]).mpr
  exact Relation.TransGen.single ⟨rfl, rfl⟩

theorem reverse_order_native :
    () ∉ (formula FirstOrderLFP.Reachability.transitive).denote (expand orderModel.toStructure).base
      (fun i => some (![true, false] i)) (fun i => i.elim0) := by
  intro h
  have hp := (FirstOrderLFP.Reachability.transitive_finite_path oneWay ![true, false]).mp
    ((expanded_formula_denote orderModel FirstOrderLFP.Reachability.transitive ![true, false] ()).mp h)
  have starts : ∀ {a b}, Relation.TransGen oneWay a b → a = false := by
    intro a b hb
    induction hb using Relation.TransGen.head_induction_on with
    | single hedge => exact hedge.1
    | head hedge _ _ => exact hedge.1
  exact Bool.false_ne_true (starts hp).symm

abbrev mixed : FOL.Signature where
  S := Bool
  Op := fun _ _ _ => Empty
  Rel := fun _ _ => Empty

def collapse : mixed ⟶ FirstOrderLFP.Reachability.signature where
  sorts _ := ()
  ops o := o.elim
  rels r := r.elim

abbrev mixedProfile : Profile mixed := ⟨2, ![false, true]⟩
abbrev mixedContext : Fin 2 → mixed.S := ![false, true]
abbrev mixedProfiles : Fin 1 → Profile mixed := fun _ => mixedProfile
abbrev mixedBodyContext : Fin 4 → mixed.S :=
  Fin.addCases (m := 2) (n := 2) (motive := fun _ : Fin 4 => mixed.S) mixedProfile.sorts mixedContext
abbrev mixedFixed : FirstOrderLFP.Formula mixed (mixedProfiles ∘ Fin.succ) mixedContext :=
  .lfp (Δ := mixedBodyContext) (by funext i; exact @Fin.addCases_left 2 2 (fun _ : Fin 4 => Bool) mixedProfile.sorts mixedContext i)
    (by funext i; exact @Fin.addCases_right 2 2 (fun _ : Fin 4 => Bool) mixedProfile.sorts mixedContext i) (.base .tt) (fun j => .var j)

theorem mixed_lfp_naturality :
    (signatureMap collapse).fixedPattern (formula mixedFixed) = formula (mixedFixed.map collapse) :=
  formula_map collapse mixedFixed

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  exact Bool.false_ne_true (h rfl)

theorem mixed_decode_naturality :
    decode (reduct collapse (expand orderModel.toStructure)) =
      (FirstOrderLFP.reduct collapse).obj (decode (expand orderModel.toStructure)) :=
  decode_reduct collapse _
end Silmaril.Logic.Matching.GuardedLFP.Examples
