module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe u v
variable {V W K J Base : Type u} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]

theorem movedSlot_absent (plan : Plan V W K J) (source : Graph V K F)
    (lowered : CFG (Option V) (Option K) F) (target : CFG (Option W) (Option J) F)
    (names : Fin n → Option V) (profile : Fin (Versioning.compile lowered).blocks.length → Ty Base)
    {candidate : ProfileCandidateFor W Base n (Versioning.compile target).blocks.length}
    (generated : profileCandidateFor plan source lowered target names profile = some candidate)
    {i : Fin n} {ty : Ty Base} (listed : (i, ty) ∈ candidate.movedSlots) :
    names i ∉ Versioning.registers lowered := by
  simp only [profileCandidateFor, Option.bind_eq_bind, Option.bind_eq_some_iff] at generated
  obtain ⟨head, _, result⟩ := generated
  cases head <;> simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at result
  all_goals try contradiction
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, eq⟩ := result
  cases eq
  obtain ⟨key, _, found⟩ := List.mem_filterMap.mp listed
  cases key with
  | none => cases found
  | some key =>
    simp only at found
    split at found
    · contradiction
    · rename_i absent
      obtain ⟨j, first, matched⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨_, _, pairEq⟩ := Option.map_eq_some_iff.mp matched
      have sameSlot : j = i := congrArg Prod.fst pairEq
      subst j
      have named : (names i).map plan.register = some key := by
        exact of_decide_eq_true (List.find?_some
          (p := fun j => decide ((names j).map plan.register = some key)) (a := i) first)
      cases h : names i with
      | none => simp [h] at named
      | some reg =>
        have eq : plan.register reg = key := Option.some.inj (by simpa only [h, Option.map_some] using named)
        subst key
        intro supported
        apply absent
        have included : reg ∈ (Versioning.registers lowered).filterMap id :=
          List.mem_filterMap.mpr ⟨some reg, supported, rfl⟩
        simpa using included

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split
