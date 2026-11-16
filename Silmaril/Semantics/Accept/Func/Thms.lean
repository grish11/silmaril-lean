module

public import Silmaril.Semantics.Accept.Func.Defs
public import Silmaril.Semantics.Accept.Rel.Thms
public import Mathlib.Data.PFun
public import Mathlib.Logic.Relator
public import Cslib.Foundations.Relation.Defs
import Silmaril.Proofs.Semantics.Accept.Func.Basic

/-!
# The functional shape of relations: laws

* bridges to Mathlib (`Relator.LeftTotal`, `RightUnique`, `RightTotal`, `LeftUnique`,
  `BiUnique`; `SetRel.dom`/`cod`/`inv`; `SetRel.exists_graph_eq_iff`; `PFun.graph'`) and to
  CSLib (`Relation.Serial`, `Relation.dom`, `Relation.cod`);
* extraction: `ofPartial_toPartial`, `toPartial_ofPartial`, `graph_toFun`, `toFun_ofTotal`;
* `ofPartial`/`ofTotal`: single-valued and functional, with totality, surjectivity and
  injectivity in terms of the function;
* closure under composition, inverse and subsets;
* pullbacks: `pullSome` and `pullAll` agree along functional relations.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

open scoped SetRel

variable {α : Type u} {β : Type v} {γ : Type w}

section Bridges

variable {R : α -|> β}

theorem total_iff_leftTotal : Total R ↔ Relator.LeftTotal (· ~[R] ·) := Iff.rfl

theorem singleValued_iff_rightUnique : SingleValued R ↔ Relator.RightUnique (· ~[R] ·) :=
  Iff.rfl

theorem surjective_iff_rightTotal : Surjective R ↔ Relator.RightTotal (· ~[R] ·) := Iff.rfl

theorem injective_iff_leftUnique : Injective R ↔ Relator.LeftUnique (· ~[R] ·) := Iff.rfl

theorem singleValued_and_injective_iff_biUnique :
    SingleValued R ∧ Injective R ↔ Relator.BiUnique (· ~[R] ·) := And.comm

theorem total_iff_dom : Total R ↔ R.dom = Set.univ := by simp [Total, Set.eq_univ_iff_forall]

theorem surjective_iff_cod : Surjective R ↔ R.cod = Set.univ := by
  simp [Surjective, Set.eq_univ_iff_forall]

@[simp] theorem total_inv : Total R.inv ↔ Surjective R := by simp [Total, Surjective]

@[simp] theorem surjective_inv : Surjective R.inv ↔ Total R := by simp [Total, Surjective]

@[simp] theorem singleValued_inv : SingleValued R.inv ↔ Injective R := by
  simp only [SingleValued, Injective, SetRel.mem_inv]
  exact ⟨fun h _ _ _ hb hb' => h hb hb', fun h _ _ _ hb hb' => h hb hb'⟩

@[simp] theorem injective_inv : Injective R.inv ↔ SingleValued R := by
  simp only [SingleValued, Injective, SetRel.mem_inv]
  exact ⟨fun h _ _ _ hb hb' => h hb hb', fun h _ _ _ hb hb' => h hb hb'⟩

theorem injective_iff_singleValued_inv : Injective R ↔ SingleValued R.inv :=
  singleValued_inv.symm

theorem functional_iff_existsUnique : Functional R ↔ ∀ a, ∃! b, a ~[R] b :=
  ⟨fun ⟨ht, hs⟩ a => (ht a).elim fun b hb => ⟨b, hb, fun _ hb' => hs hb' hb⟩,
    fun h => ⟨fun a => (h a).exists, fun _ _ _ hb hb' => (h _).unique hb hb'⟩⟩

theorem functional_iff_exists_graph : Functional R ↔ ∃! f : α → β, Function.graph f = R :=
  functional_iff_existsUnique.trans R.exists_graph_eq_iff.symm

/-- The graph of a partial function `α →. β` is single-valued. -/
theorem singleValued_graph' (f : α →. β) : SingleValued f.graph' :=
  fun _ _ _ hb hb' => Part.mem_unique hb hb'

/-- The single-valued relations are exactly the graphs of partial functions `α →. β`. -/
theorem singleValued_iff_exists_pfun : SingleValued R ↔ ∃ f : α →. β, f.graph' = R :=
  Proofs.Semantics.Accept.Func.singleValued_iff_exists_pfun

/-- CSLib: a homogeneous relation is total iff it is serial. -/
theorem total_iff_serial {R : α -|> α} : Total R ↔ Relation.Serial (· ~[R] ·) :=
  ⟨fun h => ⟨h⟩, fun h => h.serial⟩

theorem dom_eq_relation_dom : R.dom = Relation.dom (· ~[R] ·) := rfl

theorem cod_eq_relation_cod : R.cod = Relation.cod (· ~[R] ·) := rfl

end Bridges

/-! ## Function extraction -/

section Extraction

variable {R : α -|> β} {a : α} {b : β}

/-- Whatever `toPartial` picks is an output. -/
theorem mem_toPartial (h : toPartial R a = some b) : a ~[R] b :=
  Proofs.Semantics.Accept.Func.mem_toPartial h

theorem toPartial_eq_none : toPartial R a = none ↔ ∀ b, ¬ a ~[R] b :=
  Proofs.Semantics.Accept.Func.toPartial_eq_none

theorem toPartial_eq_some (hs : SingleValued R) : toPartial R a = some b ↔ a ~[R] b :=
  Proofs.Semantics.Accept.Func.toPartial_eq_some hs

@[simp] theorem pdom_toPartial : pdom (toPartial R) = R.dom :=
  Proofs.Semantics.Accept.Func.pdom_toPartial

theorem ofPartial_toPartial (hs : SingleValued R) : ofPartial (toPartial R) = R := by
  ext ⟨a, b⟩; exact toPartial_eq_some hs

theorem singleValued_ofPartial (f : α → Option β) : SingleValued (ofPartial f) :=
  fun _ _ _ hb hb' => Option.some.inj (hb.symm.trans hb')

@[simp] theorem toPartial_ofPartial (f : α → Option β) : toPartial (ofPartial f) = f := by
  funext a; cases h : f a with
  | none => exact toPartial_eq_none.2 (by simp [h])
  | some b => exact (toPartial_eq_some (singleValued_ofPartial f)).2 h

theorem mem_toFun (ht : Total R) (a : α) : a ~[R] toFun ht a := (ht a).choose_spec

theorem toFun_eq_iff (ht : Total R) (hs : SingleValued R) : toFun ht a = b ↔ a ~[R] b :=
  ⟨fun e => e ▸ mem_toFun ht a, fun hb => hs (mem_toFun ht a) hb⟩

theorem graph_toFun (ht : Total R) (hs : SingleValued R) : Function.graph (toFun ht) = R := by
  ext ⟨a, b⟩; exact toFun_eq_iff ht hs

theorem Functional.graph_toFun (h : Functional R) : Function.graph (toFun h.1) = R :=
  Accept.graph_toFun h.1 h.2

theorem total_ofTotal (f : α → β) : Total (ofTotal f) := fun a => ⟨f a, rfl⟩

theorem singleValued_ofTotal (f : α → β) : SingleValued (ofTotal f) :=
  fun _ _ _ hb hb' => hb.symm.trans hb'

theorem functional_ofTotal (f : α → β) : Functional (ofTotal f) :=
  ⟨total_ofTotal f, singleValued_ofTotal f⟩

@[simp] theorem toFun_ofTotal (f : α → β) : toFun (total_ofTotal f) = f :=
  funext fun _ => (toFun_eq_iff _ (singleValued_ofTotal f)).2 rfl

end Extraction

/-! ## Partial functions and total maps -/

section Instances

theorem total_ofPartial_iff {f : α → Option β} : Total (ofPartial f) ↔ pdom f = Set.univ := by
  rw [Set.eq_univ_iff_forall]; simp [Total, Option.isSome_iff_exists]

theorem surjective_ofPartial_iff {f : α → Option β} :
    Surjective (ofPartial f) ↔ ∀ b, ∃ a, f a = some b := Iff.rfl

/-- `ofPartial f` is injective iff `f` is injective on its domain. -/
theorem injective_ofPartial_iff {f : α → Option β} :
    Injective (ofPartial f) ↔ Set.InjOn f (pdom f) :=
  Proofs.Semantics.Accept.Func.injective_ofPartial_iff

theorem surjective_ofTotal_iff {f : α → β} : Surjective (ofTotal f) ↔ Function.Surjective f :=
  Iff.rfl

theorem injective_ofTotal_iff {f : α → β} : Injective (ofTotal f) ↔ Function.Injective f :=
  ⟨fun h _ _ e => h e rfl, fun h _ _ _ hb hb' => h (hb.trans hb'.symm)⟩

theorem oneToOne_ofTotal_iff {f : α → β} : OneToOne (ofTotal f) ↔ Function.Bijective f :=
  ⟨fun ⟨_, hi, hs⟩ => ⟨injective_ofTotal_iff.1 hi, hs⟩,
    fun ⟨hi, hs⟩ => ⟨functional_ofTotal f, injective_ofTotal_iff.2 hi, hs⟩⟩

end Instances

/-! ## Closure: composition, inverse, subsets -/

section Closure

variable {R R' : α -|> β} {S : β -|> γ}

theorem Total.comp (hR : Total R) (hS : Total S) : Total (R ○ S) := fun a =>
  let ⟨b, hb⟩ := hR a; let ⟨c, hc⟩ := hS b; ⟨c, b, hb, hc⟩

theorem SingleValued.comp (hR : SingleValued R) (hS : SingleValued S) :
    SingleValued (R ○ S) := fun _ _ _ ⟨_, hb, hc⟩ ⟨_, hb', hc'⟩ => hS hc (hR hb' hb ▸ hc')

theorem Surjective.comp (hR : Surjective R) (hS : Surjective S) : Surjective (R ○ S) := fun c =>
  let ⟨b, hb⟩ := hS c; let ⟨a, ha⟩ := hR b; ⟨a, b, ha, hb⟩

theorem Injective.comp (hR : Injective R) (hS : Injective S) : Injective (R ○ S) :=
  fun _ _ _ ⟨_, hb, hc⟩ ⟨_, hb', hc'⟩ => hR hb (hS hc' hc ▸ hb')

theorem Functional.comp (hR : Functional R) (hS : Functional S) : Functional (R ○ S) :=
  ⟨hR.1.comp hS.1, hR.2.comp hS.2⟩

theorem OneToOne.comp (hR : OneToOne R) (hS : OneToOne S) : OneToOne (R ○ S) :=
  ⟨hR.1.comp hS.1, hR.2.1.comp hS.2.1, hR.2.2.comp hS.2.2⟩

theorem OneToOne.inv (h : OneToOne R) : OneToOne R.inv :=
  ⟨⟨h.2.2, singleValued_inv.2 h.2.1⟩, injective_inv.2 h.1.2, h.1.1⟩

theorem SingleValued.mono (h : R' ⊆ R) (hs : SingleValued R) : SingleValued R' :=
  fun _ _ _ hb hb' => hs (h hb) (h hb')

theorem Injective.mono (h : R' ⊆ R) (hi : Injective R) : Injective R' :=
  fun _ _ _ ha ha' => hi (h ha) (h ha')

theorem Total.mono (h : R ⊆ R') (ht : Total R) : Total R' := fun a =>
  let ⟨b, hb⟩ := ht a; ⟨b, h hb⟩

theorem Surjective.mono (h : R ⊆ R') (hs : Surjective R) : Surjective R' := fun b =>
  let ⟨a, ha⟩ := hs b; ⟨a, h ha⟩

end Closure

/-! ## Pullbacks along functional relations -/

section Pull

variable {R : α -|> β} {L : Set β}

theorem SingleValued.pullSome_subset_pullAll (hs : SingleValued R) :
    pullSome R L ⊆ pullAll R L :=
  Accept.pullSome_subset_pullAll fun _ _ _ hb hb' => hs hb hb'

theorem Total.pullAll_subset_pullSome (ht : Total R) : pullAll R L ⊆ pullSome R L :=
  Accept.pullAll_subset_pullSome ht

theorem Functional.pullSome_eq_pullAll (h : Functional R) : pullSome R L = pullAll R L :=
  h.2.pullSome_subset_pullAll.antisymm h.1.pullAll_subset_pullSome

end Pull

end Silmaril.Accept
