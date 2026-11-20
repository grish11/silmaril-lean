module

import Silmaril.Formats.PER.Naming.Thms

open Silmaril.Formats Silmaril.Semantics.Naming

private def oracle (bytes : ByteArray) : Option Bool := if bytes.size = 0 then none else some true

private theorem oracleCompatible : PartialHashCompatible oracle (nameGraph oracle) := fun _ _ hit => hit

example : ¬ nameGraph oracle true ByteArray.empty := oracleCompatible.not_named_of_none rfl

example : UniqueNames (nameGraph oracle) ∧ ¬ Binding (nameGraph oracle) := by
  refine ⟨oracleCompatible.uniqueNames, fun bound => ?_⟩
  have same := bound (show nameGraph oracle true ⟨#[0]⟩ from rfl)
    (show nameGraph oracle true ⟨#[0, 1]⟩ from rfl)
  exact (by decide : ¬ (1 : Nat) = 2) (congrArg ByteArray.size same)

private def raw : Relation Bool Bool := graph some

private theorem rawBound : Binding raw := graph_binding some

private theorem rawUnique : UniqueNames raw := by
  intro payload firstName secondName first second
  exact Option.some.inj (first.trans second.symm)

private def aliases : PER Bool := PER.universal Bool

private def falseRepr : {repr // aliases.Dom repr} := ⟨false, trivial⟩

private def trueRepr : {repr // aliases.Dom repr} := ⟨true, trivial⟩

private def aliasClass : aliases.Quotient := Quotient.mk aliases.supportSetoid falseRepr

example : UniqueNames raw ∧ Binding (aliases.naming raw) ∧ ¬ UniqueNames (aliases.naming raw) := by
  refine ⟨rawUnique, aliases.naming_binding rawBound, fun unique => ?_⟩
  have first : false ∈ names (aliases.naming raw) aliasClass :=
    (aliases.mem_class_names falseRepr).2 ⟨false, rfl, trivial⟩
  have second : true ∈ names (aliases.naming raw) aliasClass :=
    (aliases.mem_class_names falseRepr).2 ⟨true, rfl, trivial⟩
  exact Bool.noConfusion (unique first second)

example : names (aliases.naming raw) aliasClass =
    names (aliases.naming raw) (Quotient.mk aliases.supportSetoid trueRepr) :=
  aliases.class_names_congr trivial

example : (aliases.naming_binding rawBound).lookup true = some aliasClass :=
  (Binding.lookup_eq_some _).2 ((aliases.mem_class_names falseRepr).2 ⟨true, rfl, trivial⟩)

private def onlyTrue : PER Bool := aliases.restrict (· = true)

private def onlyTrueRepr : {repr // onlyTrue.Dom repr} := ⟨true, ⟨rfl, rfl, trivial⟩⟩

example : false ∉ names (onlyTrue.naming raw) (Quotient.mk onlyTrue.supportSetoid onlyTrueRepr) := by
  intro claimed
  obtain ⟨otherRepr, hit, equivalent⟩ := (onlyTrue.mem_class_names onlyTrueRepr).1 claimed
  have same : false = otherRepr := Option.some.inj hit
  exact Bool.noConfusion (same.trans equivalent.1)

example : rawBound.lookup false = some false ∧ (onlyTrue.naming_binding rawBound).lookup false = none := by
  classical
  have present : rawBound.lookup false = some false := (Binding.lookup_eq_some rawBound).2 rfl
  refine ⟨present, ?_⟩
  have invalid : ¬ onlyTrue.Dom false := fun valid => Bool.noConfusion valid.1
  rw [onlyTrue.naming_lookup rawBound, present]
  change onlyTrue.projectClass false = none
  rw [PER.projectClass, dite_eq_right invalid]
