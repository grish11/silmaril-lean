module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.SetTheory ZFSet
open Silmaril.Logic.SetTheory

universe u v w

private theorem pair_ne_empty (a b : ZFSet.{u}) : ZFSet.pair a b ≠ ∅ := by
  intro h
  have ha : ({a} : ZFSet.{u}) ∈ ZFSet.pair a b := by simp [ZFSet.pair]
  exact notMem_empty _ (h ▸ ha)

theorem path_encode_injective {α : Type v} {e : α → ZFSet.{u}}
    (he : Function.Injective e) : Function.Injective (PathCode.encode e) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons a ys => exact (pair_ne_empty _ _ h.symm).elim
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil => exact (pair_ne_empty _ _ h).elim
    | cons b ys =>
      obtain ⟨hab, hxy⟩ := ZFSet.pair_inj.mp h
      exact congrArg₂ List.cons (he hab) (ih hxy)

theorem stage_mem {U D : ZFSet.{u}} (hU : IsGrothendieckUniverse U) (hD : D ∈ U) :
    ∀ n, PathCode.stage D n ∈ U
  | 0 => hU.singleton_mem hU.empty_mem
  | n + 1 => hU.insert_mem hU.empty_mem (hU.prod_mem hD (stage_mem hU hD n))

theorem omegaIndex_numeral (n : ℕ) :
    PathCode.omegaIndex (⟨numeral n, numeral_mem_omega n⟩ : (omega : ZFSet.{u})) = n := by
  apply numeral_injective
  exact Classical.choose_spec (mem_omega_iff.mp (numeral_mem_omega n))

theorem lists_mem {U D : ZFSet.{u}} (hU : IsGrothendieckUniverse U) (hD : D ∈ U) :
    PathCode.lists D ∈ U :=
  hU.iUnion_mem omega hU.omega_mem _ (fun n => stage_mem hU hD (PathCode.omegaIndex n))

theorem path_encode_mem_stage {α : Type v} {D : ZFSet.{u}} {e : α → ZFSet.{u}}
    (he : ∀ a, e a ∈ D) (xs : List α) : PathCode.encode e xs ∈ PathCode.stage D xs.length := by
  induction xs with
  | nil => exact mem_singleton.mpr rfl
  | cons a xs ih =>
    exact mem_insert_iff.mpr (.inr (pair_mem_prod.mpr ⟨he a, ih⟩))

theorem path_encode_mem_lists {α : Type v} {D : ZFSet.{u}} {e : α → ZFSet.{u}}
    (he : ∀ a, e a ∈ D) (xs : List α) : PathCode.encode e xs ∈ PathCode.lists D := by
  apply mem_iUnion.mpr
  refine ⟨⟨numeral xs.length, numeral_mem_omega _⟩, ?_⟩
  rw [omegaIndex_numeral]
  exact path_encode_mem_stage he xs

theorem observe_injective {α : Type v} {β : α → Type w} :
    Function.Injective (WSet.observe (β := β)) := by
  intro t
  induction t with
  | mk a f ih =>
    intro s h
    cases s with
    | mk a' f' =>
      have ha : a = a' := Option.some.inj (congrFun h [])
      subst a'
      congr 1
      funext b
      apply ih b
      funext xs
      have hv := congrFun h (⟨a, b⟩ :: xs)
      simpa [WSet.observe] using hv

theorem branchCode_injective {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    Function.Injective (WSet.branchCode (A := A) (B := B)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp h
  have haa : a = a' := Subtype.ext ha
  subst a'
  congr 1
  exact Subtype.ext hb

theorem branchCode_mem {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (b : WSet.Branch (fun a : A => B a.val)) : WSet.branchCode b ∈ SetSem.sigma A B :=
  SetSem.pair_mem_sigma.mpr ⟨b.1.property, b.2.property⟩

theorem observationBound_mem {U A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) (hA : A ∈ U) (hB : ∀ a ∈ A, B a ∈ U) :
    WSet.observationBound A B ∈ U :=
  hU.prod_mem (lists_mem hU (SetSem.sigma_mem hU hA hB)) hA

theorem pair_mem_encode {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (t : WSet.Tree A B) (xs : List (WSet.Branch (fun a : A => B a.val))) (a : A) :
    ZFSet.pair (PathCode.encode WSet.branchCode xs) a.val ∈ WSet.encode t ↔
      WSet.observe t xs = some a := by
  rw [WSet.encode, mem_sep]
  constructor
  · rintro ⟨_, ys, b, hb, hab⟩
    obtain ⟨hxs, ha⟩ := ZFSet.pair_inj.mp hab
    have he : ys = xs := path_encode_injective branchCode_injective hxs
    have hea : b = a := Subtype.ext ha
    simpa only [he, hea] using hb
  · intro ha
    refine ⟨pair_mem_prod.mpr ⟨path_encode_mem_lists branchCode_mem xs, a.property⟩, ?_⟩
    exact ⟨xs, a, ha, rfl⟩

theorem encode_injective {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    Function.Injective (WSet.encode (A := A) (B := B)) := by
  intro t s h
  apply observe_injective
  funext xs
  have hh : ∀ a : A, WSet.observe t xs = some a ↔ WSet.observe s xs = some a := by
    intro a
    rw [← pair_mem_encode, h, pair_mem_encode]
  cases ht : WSet.observe t xs with
  | none =>
    cases hs : WSet.observe s xs with
    | none => rfl
    | some a => exact ht.symm.trans ((hh a).mpr hs)
  | some a => exact ((hh a).mp ht).symm

theorem encode_mem_carrier {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (t : WSet.Tree A B) :
    WSet.encode t ∈ WSet.carrier A B := by
  exact mem_sep.mpr ⟨mem_powerset.mpr sep_subset, t, rfl⟩

theorem mem_carrier_iff {A z : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    z ∈ WSet.carrier A B ↔ ∃ t : WSet.Tree A B, WSet.encode t = z := by
  constructor
  · intro hz
    exact (mem_sep.mp hz).2
  · rintro ⟨t, rfl⟩
    exact encode_mem_carrier t

/-- Closure of the entire W-type, rather than just its individual tree codes. -/
theorem carrier_mem {U A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) (hA : A ∈ U) (hB : ∀ a ∈ A, B a ∈ U) :
    WSet.carrier A B ∈ U :=
  hU.subset_mem (hU.powerset_mem _ (observationBound_mem hU hA hB)) sep_subset


/-- Changing fibres outside the label set cannot change the encoded carrier. -/
theorem carrier_congr {A : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = C a) : WSet.carrier A B = WSet.carrier A C := by
  have hfamily : (fun a : A => B a.val) = (fun a : A => C a.val) :=
    funext fun a => h a.val a.property
  have hbound : WSet.observationBound A B = WSet.observationBound A C :=
    congrArg (fun D => ZFSet.prod (PathCode.lists D) A) (SetSem.sigma_congr h)
  unfold WSet.carrier WSet.encode WSet.branchCode WSet.Tree WSet.Branch
  rw [hbound]
  let F (β : A → ZFSet.{u}) : ZFSet.{u} :=
    (WSet.observationBound A C).powerset.sep fun z =>
      ∃ t : WType (fun a : A => β a),
        (WSet.observationBound A C).sep (fun z =>
          ∃ (xs : List (Σ a : A, β a)) (a : A),
            WSet.observe t xs = some a ∧
              ZFSet.pair (PathCode.encode (fun b => ZFSet.pair b.1.val b.2.val) xs) a.val = z) = z
  exact congrArg F hfamily

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT
