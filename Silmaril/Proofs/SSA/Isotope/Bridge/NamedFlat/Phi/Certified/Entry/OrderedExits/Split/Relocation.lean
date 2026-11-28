module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation

open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse (Register Registers)
open Silmaril.SSA.LambdaRTL (Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut (reads)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation

universe u

private theorem base_le (base : Nat) (xs : List Nat) : base ≤ xs.foldr max base := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih.trans (Nat.le_max_right x _)

private theorem member_le (base : Nat) {xs : List Nat} {x : Nat} (mem : x ∈ xs) : x ≤ xs.foldr max base := by
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact Nat.le_max_left x _
    · exact (ih tail).trans (Nat.le_max_right y _)

private theorem lookup_mem {needed : List Demand.{u}} {depth : Nat} {name : Register.{u}}
    (found : needed.lookup depth = some name) : (depth, name) ∈ needed := by
  obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem infer_valid (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) {allocation : Registers Register.{u}}
    (found : infer captures parameter previous needed = some allocation) :
    Valid captures parameter previous needed allocation := by
  unfold infer at found
  dsimp only at found
  split at found
  next passed =>
    cases Option.some.inj found
    simp only [Bool.and_eq_true, compatible, satisfies, decide_eq_true_eq, List.all_eq_true] at passed
    obtain ⟨⟨⟨paramBound, forcedOutside⟩, forcedInjective⟩, follows⟩ := passed
    let start := firstSpare captures parameter previous needed
    have afterForced {depth : Nat} {name : Register.{u}} (hit : needed.lookup depth = some name) :
        name.down < start := by
      have mem : name.down ∈ (previous.map ULift.down ++ needed.map fun pair => pair.2.down) :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(depth, name), lookup_mem hit, rfl⟩)
      exact Nat.lt_succ_of_le (member_le _ mem)
    have afterParam : parameter.down < start :=
      Nat.lt_succ_of_le ((Nat.le_max_right _ _).trans (base_le _ _))
    refine ⟨rfl, paramBound, ?_, ?_, follows, ?_⟩
    · intro left right equal
      cases foundLeft : needed.lookup left <;> cases foundRight : needed.lookup right
      · simp only [complete, foundLeft, foundRight, Option.getD_none] at equal
        exact Nat.add_left_cancel (congrArg ULift.down equal)
      · rename_i name
        simp only [complete, foundLeft, foundRight, Option.getD_none, Option.getD_some] at equal
        have impossible : start + left = name.down := congrArg ULift.down equal
        have bound := afterForced foundRight
        omega
      · rename_i name
        simp only [complete, foundLeft, foundRight, Option.getD_none, Option.getD_some] at equal
        have impossible : name.down = start + right := congrArg ULift.down equal
        have bound := afterForced foundLeft
        omega
      · simp only [complete, foundLeft, foundRight, Option.getD_some] at equal
        exact forcedInjective _ (lookup_mem foundLeft) _ (lookup_mem foundRight) equal
    · intro depth
      cases hit : needed.lookup depth with
      | some name =>
        simpa only [complete, hit, Option.getD_some] using forcedOutside (depth, name) (lookup_mem hit)
      | none =>
        change captures ≤ ((needed.lookup depth).getD ⟨start + depth⟩).down ∧
          (needed.lookup depth).getD ⟨start + depth⟩ ≠ parameter
        rw [hit, Option.getD_none]
        refine ⟨by change captures ≤ start + depth; omega, ?_⟩
        intro eq
        have down : start + depth = parameter.down := congrArg ULift.down eq
        omega
    · intro depth absent name prior equal
      simp only [complete, absent, Option.getD_none] at equal
      have down : start + depth = name.down := congrArg ULift.down equal
      have mem : name.down ∈ (previous.map ULift.down ++ needed.map fun pair => pair.2.down) :=
        List.mem_append_left _ (List.mem_map.mpr ⟨name, prior, rfl⟩)
      have above : name.down < start := Nat.lt_succ_of_le (member_le _ mem)
      omega
  next => cases found

theorem readDemands_iff {allocation : Registers Register.{u}} {parameter : Register.{u}}
    (fixed : allocation.parameter = parameter) {value : Val Origin} {fields : List Register.{u}} :
    renameValue allocation value = reads fields ↔
      ∃ needed, readDemands parameter value fields = some needed ∧
        ∀ r ∈ needed, allocation.localAt r.1 = r.2 := by
  induction fields generalizing value with
  | nil =>
    cases value <;> simp [reads, renameValue, readDemands]
  | cons name rest ih =>
    cases value with
    | var => simp [reads, renameValue, readDemands]
    | unit => simp [reads, renameValue, readDemands]
    | pair head tail =>
      cases head with
      | unit => simp [reads, renameValue, readDemands]
      | pair => simp [reads, renameValue, readDemands]
      | var origin =>
        have tailEq := ih (value := tail)
        cases found : readDemands parameter tail rest with
        | none =>
          have missing : renameValue allocation tail ≠ reads rest := by
            simpa [found] using tailEq
          cases origin <;> simp [reads, renameValue, readDemands, found, missing]
        | some requests =>
          have tailGood : renameValue allocation tail = reads rest ↔
              ∀ r ∈ requests, allocation.localAt r.1 = r.2 := by
            simpa [found] using tailEq
          cases origin with
          | input slot =>
            by_cases h : name = ⟨slot⟩ <;>
              simp [reads, renameValue, readDemands, Origin.register, found, tailGood, h,
                Ne.symm]
          | parameter =>
            by_cases h : name = parameter <;>
              simp [reads, renameValue, readDemands, Origin.register, fixed, found, tailGood, h,
                Ne.symm]
          | «local» depth =>
            simp only [reads, renameValue, readDemands, Origin.register, found, Option.bind_eq_bind,
              Option.bind_some, Option.some.injEq, Val.pair.injEq, Val.var.injEq,
              tailGood]
            exact ⟨fun h => ⟨_, rfl, List.forall_mem_cons.mpr h⟩, fun ⟨_, rfl, h⟩ =>
              List.forall_mem_cons.mp h⟩

theorem constraints_of_valid {captures : Nat} {parameter : Register.{u}} {prior : List Register.{u}}
    {needed : List Demand.{u}} {allocation : Registers Register.{u}}
    (valid : Valid captures parameter prior needed allocation) :
    Constraints captures parameter needed := by
  refine ⟨valid.sameParameter ▸ valid.parameterOutside, ?_, ?_, ?_⟩
  · intro request member
    simpa only [valid.reads request member, valid.sameParameter] using valid.localsOutside request.1
  · intro a ha b hb same
    rw [← valid.reads a ha, ← valid.reads b hb, same]
  · intro a ha b hb same
    exact valid.distinctLocals ((valid.reads a ha).trans (same.trans (valid.reads b hb).symm))

private theorem lookup_of_consistent {needed : List Demand.{u}} {request : Demand.{u}}
    (mem : request ∈ needed) (same : ∀ r ∈ needed, r.1 = request.1 → r.2 = request.2) :
    needed.lookup request.1 = some request.2 := by
  induction needed with
  | nil => simp at mem
  | cons r rest ih =>
    rcases r with ⟨depth, name⟩
    rw [List.lookup_cons]
    by_cases hit : request.1 = depth
    · rw [beq_iff_eq.mpr hit]
      exact congrArg some (same (depth, name) List.mem_cons_self hit.symm)
    · rw [beq_eq_false_iff_ne.mpr hit]
      exact ih ((List.mem_cons.mp mem).resolve_left (fun eq => hit (congrArg Prod.fst eq)))
        (fun other inside => same other (List.mem_cons_of_mem _ inside))

theorem infer_of_constraints {captures : Nat} {parameter : Register.{u}} (prior : List Register.{u})
    {needed : List Demand.{u}} (constraints : Constraints captures parameter needed) :
    infer captures parameter prior needed = some (complete captures parameter prior needed) := by
  have fits : compatible captures parameter needed = true := by
    simp only [compatible, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨constraints.parameterOutside, constraints.localsOutside⟩, constraints.oneDepthPerName⟩
  have follows : satisfies (complete captures parameter prior needed) needed = true := by
    simp only [satisfies, List.all_eq_true]
    intro request mem
    have hit := lookup_of_consistent mem (fun r h => constraints.oneNamePerDepth r h request mem)
    cases request
    exact decide_eq_true (by simp [complete, hit])
  simp [infer, fits, follows]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation
