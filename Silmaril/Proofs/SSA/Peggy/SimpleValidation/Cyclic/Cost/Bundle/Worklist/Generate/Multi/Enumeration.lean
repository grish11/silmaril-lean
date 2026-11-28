module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG (Classes)
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate (bindAt_available bindAt_matches)
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable [DecidableEq Data]
variable {classes : Classes n} {layout : Layout g}

private theorem mem_targets (port : layout.Port) (i : Fin layout.size) :
    i ∈ targets classes layout port ↔
      g.sort (layout.rep i) = (g.node (layout.rep port.1)).inputs[port.2] ∧
      classes (layout.rep i) = classes (layout.required port).id := by
  simp only [targets, List.mem_filter, List.mem_finRange, true_and]
  exact bindAt_available (layout := layout.skeleton) (layout.required port) i

private theorem mem_enumerate (ports : List layout.Port) (assignment : List layout.Binding) :
    assignment ∈ enumerate classes layout ports ↔
      assignment.map Prod.fst = ports ∧
        ∀ binding ∈ assignment,
          g.sort (layout.rep binding.2) = (g.node (layout.rep binding.1.1)).inputs[binding.1.2] ∧
          classes (layout.rep binding.2) = classes (layout.required binding.1).id := by
  induction ports generalizing assignment with
  | nil => cases assignment <;> simp [enumerate]
  | cons port ports ih =>
    cases assignment with
    | nil => simp [enumerate]
    | cons binding tail =>
      rcases binding with ⟨key, addr⟩
      simp only [enumerate, List.mem_flatMap, List.mem_map, List.cons.injEq, Prod.mk.injEq,
        List.map_cons, List.forall_mem_cons, mem_targets]
      constructor
      · rintro ⟨target, good, suffix, listed, ⟨rfl, rfl⟩, sameTail⟩
        subst suffix
        obtain ⟨keys, compatible⟩ := (ih tail).mp listed
        exact ⟨⟨rfl, keys⟩, good, compatible⟩
      · rintro ⟨⟨rfl, keys⟩, good, compatible⟩
        exact ⟨addr, good, tail, (ih tail).mpr ⟨keys, compatible⟩, ⟨rfl, rfl⟩, rfl⟩

theorem mem_choices (assignment : List layout.Binding) :
    assignment ∈ choices classes layout ↔ ValidAssignment classes layout assignment := by
  by_cases distinct : layout.vary.Nodup <;> simp [choices, ValidAssignment, distinct, mem_enumerate]

omit [DecidableEq Data] in
private theorem port_eq_of_slots {a b : layout.Port}
    (row : a.1 = b.1) (slot : a.2.val = b.2.val) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  change i = j at row
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext slot)

omit [DecidableEq Data] in
private theorem addressAt_of_mem {assignment : List layout.Binding} {port : layout.Port}
    {addr : Fin layout.size} (distinct : (assignment.map Prod.fst).Nodup)
    (listed : (port, addr) ∈ assignment) :
    addressAt layout assignment port.1 port.2.val = some addr := by
  induction assignment with
  | nil => simp at listed
  | cons first tail ih =>
    obtain ⟨other, target⟩ := first
    rw [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp listed with same | later
    · cases same
      simp [addressAt]
    · have different : ¬ (port.1 = other.1 ∧ port.2.val = other.2.val) := by
        rintro ⟨row, slot⟩
        have present : port ∈ tail.map Prod.fst := List.mem_map.mpr ⟨(port, addr), later, rfl⟩
        exact distinct.1 ((port_eq_of_slots row slot) ▸ present)
      simpa [addressAt, different] using ih distinct.2 later

theorem resolve_assigned {assignment : List layout.Binding}
    (valid : ValidAssignment classes layout assignment) {port : layout.Port}
    {addr : Fin layout.size} (listed : (port, addr) ∈ assignment) :
    ∃ ref, resolve classes layout assignment port.1 port.2.val (layout.required port) = some ref ∧
      ref.id = addr := by
  have distinct : (assignment.map Prod.fst).Nodup := valid.2.1.symm ▸ valid.1
  have compatible := valid.2.2 (port, addr) listed
  obtain ⟨ref, hit⟩ := Option.isSome_iff_exists.mp
    ((bindAt_available (layout := layout.skeleton) (layout.required port) addr).mpr compatible)
  refine ⟨ref, ?_, (bindAt_matches _ hit).1⟩
  rw [resolve, addressAt_of_mem distinct listed]
  exact hit

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi
