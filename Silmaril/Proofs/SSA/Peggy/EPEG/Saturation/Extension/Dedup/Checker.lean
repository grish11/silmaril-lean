module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
import Mathlib.Data.Fin.Tuple.Basic

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site i : Fin n} {zero : P [] .count}

private theorem ref_eq {t : Ty Data} {a b : Ref g.sort t} (eq : a.id = b.id) : a = b := by
  cases a
  cases b
  cases eq
  rfl

private theorem key_eq {t : Ty Data} (node : Node P params (Fin l) g.sort t)
    (loop : Fin l) (initial : Ref g.sort t) (count : Ref g.sort .count) :
    evalKey node = some (loop, initial.id, count.id) →
      node = Node.ofLabel (.eval loop) (.cons initial (.cons count .nil)) := by
  obtain ⟨_, label, args⟩ := node
  cases label with
  | eval key =>
    cases args with
    | cons a rest =>
      cases rest with
      | cons b rest =>
        cases rest
        intro h
        have eq : (key, a.id, b.id) = (loop, initial.id, count.id) := Option.some.inj h
        have loops : key = loop := congrArg Prod.fst eq
        have first := ref_eq (congrArg (fun k => k.2.1) eq)
        have second := ref_eq (congrArg (fun k => k.2.2) eq)
        subst loop initial count
        rfl
  | _ => intro h; cases h

private theorem key_iff {t t' : Ty Data} (eq : t = t') (node : Node P params (Fin l) g.sort t)
    (loop : Fin l) (initial : Ref g.sort t') (count : Ref g.sort .count) :
    evalKey node = some (loop, initial.id, count.id) ↔
      HEq node (Node.ofLabel (P := P) (params := params) (.eval loop)
        (.cons initial (.cons count .nil))) := by
  subst t'
  exact ⟨fun h => heq_of_eq (key_eq node loop initial count h),
    fun h => (eq_of_heq h).symm ▸ rfl⟩

theorem check_rhs_iff [DecidableEq Data] (found : ZeroSample g site zero) :
    checkRhs found i = true ↔ RhsAt found i := by
  simp only [checkRhs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun ⟨sort, key⟩ => ⟨sort, (key_iff sort _ _ _ _).mp key⟩,
    fun h => ⟨h.sort_eq, (key_iff h.sort_eq _ _ _ _).mpr h.shape⟩⟩

theorem check_covered_iff [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n) :
    checkCovered found classes = true ↔ Covered found classes := by
  simp only [checkCovered, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, beq_iff_eq,
    check_rhs_iff, Covered]

theorem keep_iff [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n) :
    choose found classes = .keep ↔ Covered found classes := by
  rw [← check_covered_iff]
  unfold choose
  split
  · simp_all
  · split <;> simp_all

theorem reuse_sound [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n)
    (choice : choose found classes = .reuse i) : RhsAt found i := by
  unfold choose at choice
  split at choice
  · cases choice
  · split at choice
    · rename_i rhs h
      cases choice
      exact (check_rhs_iff found).mp (List.find?_some h)
    · cases choice

theorem append_iff [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n) :
    choose found classes = .append ↔ ∀ i, ¬ RhsAt found i := by
  constructor
  · intro choice i hit
    unfold choose at choice
    split at choice
    · cases choice
    · split at choice
      · cases choice
      · rename_i absent
        exact (List.find?_eq_none.mp absent i (List.mem_finRange i)) ((check_rhs_iff found).mpr hit)
  · intro absent
    have missing : (List.finRange n).find? (checkRhs found) = none :=
      List.find?_eq_none.mpr fun i _ yes => absent i ((check_rhs_iff found).mp yes)
    have uncovered : checkCovered found classes = false := by
      cases h : checkCovered found classes
      · rfl
      · obtain ⟨i, hit, _⟩ := (check_covered_iff found classes).mp h
        exact (absent i hit).elim
    simp [choose, missing, uncovered]

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup
