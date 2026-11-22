module

import Silmaril.ProofFormats.DaslSyntax.HOL.Thms
import Silmaril.ProofFormats.DaslSyntax.MLTT.Thms
import Silmaril.ProofFormats.DaslSyntax.MLTT.Semantics.Thms
import Silmaril.ProofFormats.DaslSyntax.PA.Thms
import Silmaril.ProofFormats.DaslSyntax.FOL.Thms
import Silmaril.Logic.Concrete.SExp.Thms
import Mathlib.Tactic.FinCases

open Silmaril.Formats.Dasl
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.Semantics.Naming (graph graph_binding)
open Silmaril.Logic.TypeTheory.ExtensionalMLTT (ECtx ETm)
open Silmaril.Logic.Arithmetic (Sentence paZeroAddZero)
open Silmaril.Consequence.FirstOrder (orderOps orderRels irrefl)

namespace DaslLogicTest

def paSentence : Sentence := .equal (.add .zero .zero) .zero

def dependentContext : ECtx := .cons .nil "univ" .unit

def getObject (withWitness : Bool) : Nat → Option (Shallow Nat)
  | 0 => some (Encode.list.encode [.string "=", .ref (.obj 1), .ref (.obj 2)])
  | 1 => some (Encode.list.encode [.string "+", .ref (.obj 2), .ref (.obj 2)])
  | 2 => some (.string "zero")
  | 3 => some (Encode.list.encode [.string "ctx", .ref (.obj 4)])
  | 4 => some (.string "bool")
  | 5 => some (Encode.list.encode [.string "bvar", .string (Nat.repr 0)])
  | 6 => some (Encode.list.encode [.string "ctx", .ref (.obj 7)])
  | 7 => some (Encode.list.encode [.string "univ", .ref (.obj 8)])
  | 8 => some (.string "unit")
  | 9 => if withWitness then some (.string "star") else none
  | 10 => some (.string "true")
  | _ => none

def storeFor (withWitness : Bool) : Store Nat := ⟨graph (getObject withWitness), graph fun _ => none⟩

def store : Store Nat := storeFor true

theorem store_binding : store.Binding := ⟨graph_binding _, graph_binding _⟩

private theorem list_ext {size : Nat} {left right : Fin size → Value}
    (same : ∀ index, left index = right index) : Tree.list size left = Tree.list size right :=
  congrArg (Tree.list size) (funext same)

def paNamed : Named Nat := Encode.list.encode [.string "=", Tree.obj 1
  (Encode.list.encode [.string "+", Tree.obj 2 (.string "zero"), Tree.obj 2 (.string "zero")]),
  Tree.obj 2 (.string "zero")]

theorem pa_expands : FullNames store 0 paNamed := by
  have zero : Expands store (.ref (.obj 2)) (Tree.obj 2 (.string "zero")) := .obj rfl (.string _)
  refine ⟨_, rfl, Expands.list ?_⟩
  intro index
  change Fin 3 at index
  fin_cases index
  · exact .string _
  · refine .obj rfl (Expands.list ?_)
    intro child
    change Fin 3 at child
    fin_cases child
    · exact .string _
    · exact zero
    · exact zero
  · exact zero

theorem pa_root : (PA.formula 0).names store 0 paSentence := by
  refine ⟨_, ⟨paNamed, pa_expands, rfl⟩, linkAll, ?_⟩
  change (PA.formula 0).write linkAll paSentence = paNamed.erase
  simp only [Syntax.write, PA.formula, ofSExpCodec, Silmaril.Logic.Arithmetic.SExp.codec, paSentence,
    Silmaril.Logic.Arithmetic.SExp.encodeFormula, Silmaril.Logic.Arithmetic.SExp.encodeTerm]
  refine list_ext (size := 3) ?_
  intro index
  fin_cases index
  · rfl
  · apply congrArg Value.obj
    refine list_ext (size := 3) ?_
    intro child
    fin_cases child <;> rfl
  · rfl

theorem pa_theorem : 0 ∈ PA.theorems store :=
  Syntax.mem_namesWhere.mpr ⟨paSentence, pa_root, ⟨paZeroAddZero⟩⟩

theorem pa_sentence : 0 ∈ PA.sentences store := Syntax.mem_namesWhere.mpr ⟨paSentence, pa_root, trivial⟩

theorem pa_truth : 0 ∈ PA.standardTruth store := PA.theorems_subset_standardTruth store pa_theorem

example : (PA.formula 0).recover ((PA.formula 0).write (· == [1]) paSentence) = some paSentence :=
  (PA.formula 0).recover_write _ _

example : (PA.formula 0).normalize ((PA.formula 0).write (· == [1]) paSentence) =
    some ((PA.formula 0).write linkAll paSentence) :=
  Syntax.normalize_of_optional ⟨(· == [1]), rfl⟩

example : (PA.term 0).recover (render PA.slots inlineAll
    (.list [.atom "var", Silmaril.Logic.Concrete.SExp.num 0])) = none := by
  rw [Syntax.recover, read_render, Option.bind_some]
  simp [PA.term, Silmaril.Logic.Arithmetic.SExp.readTerm?, Silmaril.Logic.Concrete.SExp.num?_num]

example : (PA.formula 0).recover (Encode.list.encode [.string "=", .string "zero"]) = none := rfl

def holContext : Named Nat := Encode.list.encode [.string "ctx", Tree.obj 4 (.string "bool")]

theorem hol_context_expands : FullNames store 3 holContext := by
  refine ⟨_, rfl, Expands.list ?_⟩
  intro index
  change Fin 2 at index
  fin_cases index
  · exact .string _
  · exact .obj rfl (.string _)

theorem hol_typing : HOL.typing store Silmaril.Logic.HOLLight.initialSignature 3 5 4 := by
  have bvar : FullNames store 5 (Encode.list.encode [.string "bvar", .string (Nat.repr 0)]) := by
    refine ⟨_, rfl, Expands.list ?_⟩
    intro index
    change Fin 2 at index
    fin_cases index <;> exact .string _
  have contextForm : HOL.ctx.codec.encode [.bool] = .list [.atom "ctx", .atom "bool"] := by
    change (taggedList "ctx").encode (HOL.ty.codec.listCodec.encode [.bool]) = _
    rw [Encode.TotalCodec.listCodec_encode]
    rfl
  have presentsContext : HOL.ctx.presents linkAll holContext.erase [.bool] := by
    change render HOL.slots linkAll (HOL.ctx.codec.encode [.bool]) = holContext.erase
    rw [contextForm]
    refine list_ext (size := 2) ?_
    intro index
    fin_cases index <;> rfl
  have presentsTerm : HOL.tm.presents linkAll
      (Named.erase (Name := Nat) (Encode.list.encode [.string "bvar", .string (Nat.repr 0)])) (.bvar 0) := by
    change HOL.tm.write linkAll (.bvar 0) = _
    refine list_ext (size := 2) ?_
    intro index
    fin_cases index <;> rfl
  exact ⟨([.bool], .bvar 0, .bool, ()),
    ⟨⟨_, ⟨holContext, hol_context_expands, rfl⟩, linkAll, presentsContext⟩,
     ⟨_, ⟨_, bvar, rfl⟩, linkAll, presentsTerm⟩,
     ⟨_, ⟨_, ⟨_, rfl, .string "bool"⟩, rfl⟩, linkAll, rfl⟩, trivial⟩,
    .bvar rfl trivial⟩

def mlttContext : Named Nat := Encode.list.encode [.string "ctx", Tree.obj 7
  (Encode.list.encode [.string "univ", Tree.obj 8 (.string "unit")])]

theorem mltt_context_expands {withWitness : Bool} : FullNames (storeFor withWitness) 6 mlttContext := by
  refine ⟨_, rfl, Expands.list ?_⟩
  intro index
  change Fin 2 at index
  fin_cases index
  · exact .string _
  · refine .obj rfl (Expands.list ?_)
    intro child
    change Fin 2 at child
    fin_cases child
    · exact .string _
    · exact .obj rfl (.string _)

theorem mltt_context_root {withWitness : Bool} : MLTT.ctx.names (storeFor withWitness) 6 dependentContext := by
  refine ⟨_, ⟨mlttContext, mltt_context_expands, rfl⟩, linkAll, ?_⟩
  change MLTT.ctx.write linkAll dependentContext = mlttContext.erase
  refine list_ext (size := 2) ?_
  intro index
  fin_cases index
  · rfl
  · apply congrArg Value.obj
    refine list_ext (size := 2) ?_
    intro child
    fin_cases child <;> rfl

theorem mltt_context_ok : MLTT.wellFormed dependentContext :=
  .cons_ok .nil_ok (by simp [ECtx.dv]) (ECtx.JEq.unit (n := 0) .nil_ok)

theorem mltt_unit_root {withWitness : Bool} : MLTT.ty.names (storeFor withWitness) 8 .unit :=
  ⟨_, ⟨_, ⟨_, rfl, .string "unit"⟩, rfl⟩, linkAll, rfl⟩

theorem mltt_checks_star : MLTT.checks dependentContext .unit .star := ⟨mltt_context_ok, mltt_context_ok⟩

theorem mltt_inhabits : MLTT.inhabitance (storeFor false) 6 8 :=
  system_iff.mpr ⟨dependentContext, .unit, mltt_context_root, mltt_unit_root, .star, mltt_checks_star⟩

example : ¬ ∃ shallow, (storeFor false).objects 9 shallow := by
  rintro ⟨_, hit⟩
  cases hit

theorem mltt_star_root : (MLTT.tm 0).names store 9 .star :=
  ⟨_, ⟨_, ⟨_, rfl, .string "star"⟩, rfl⟩, linkAll, rfl⟩

theorem mltt_fixed_type : 9 ∈ MLTT.wellTyped store dependentContext .unit :=
  Syntax.mem_namesWhere.mpr ⟨.star, mltt_star_root, mltt_checks_star⟩

theorem mltt_typing : MLTT.typing store 6 9 8 :=
  ⟨(dependentContext, .star, .unit, ()), ⟨mltt_context_root, mltt_star_root, mltt_unit_root, trivial⟩,
    mltt_checks_star⟩

theorem mltt_length_nat : MLTT.lenNat store 6 1 :=
  ⟨(dependentContext, (1 : Nat), ()), ⟨mltt_context_root, rfl, trivial⟩, rfl⟩

theorem mltt_length_i64 : MLTT.lenI64 store 6 (.i64 1) :=
  (MLTT.lenI64_iff store 6 (.i64 1)).mpr ⟨1, mltt_length_nat, rfl, by decide⟩

example : ¬ Lift.natI64 (.i64 0) (2^64) := fun repr => Nat.not_lt_of_ge (by decide) repr.2

example : (UInt64.ofNat (2^63 - 1)).toInt64.toInt = 9223372036854775807 :=
  Lift.natI64_exact (number := 2^63 - 1) (by decide)

def orderLabels := FOL.Labels.identity orderOps orderRels

theorem fol_true_root : (FOL.formula orderLabels 0).names store 10 .tt :=
  ⟨_, ⟨_, ⟨_, rfl, .string "true"⟩, rfl⟩, linkAll, rfl⟩

theorem fol_sentence : 10 ∈ FOL.sentences store orderLabels :=
  Syntax.mem_namesWhere.mpr ⟨.tt, fol_true_root, trivial⟩

theorem fol_valid : 10 ∈ FOL.valid store orderLabels :=
  Syntax.mem_namesWhere.mpr ⟨.tt, fol_true_root, fun _ => trivial⟩

example : (FOL.formula orderLabels 0).recover ((FOL.formula orderLabels 0).write linkAll irrefl) = some irrefl :=
  (FOL.formula orderLabels 0).recover_write _ _

example : ((FOL.term orderLabels 0).recover (render FOL.slots linkAll (.list [.atom "app", .atom "succ"]))).isNone := by
  rw [Syntax.recover, read_render, Option.bind_some]
  rfl

#print axioms Silmaril.Semantics.Naming.Lift.matches_binding
#print axioms Silmaril.Semantics.Naming.Lift.rel_iff_of_match
#print axioms Syntax.recover_write
#print axioms Syntax.named_binding
#print axioms Syntax.mem_namesWhere_language
#print axioms Lift.natI64_exact
#print axioms Lift.orderedSet_encode
#print axioms Lift.codedSet_binding
#print axioms HOL.derives_iff_derivesFromSet
#print axioms HOL.entails_iff_entailsWith
#print axioms HOL.derives_le_entails
#print axioms FOL.theorems_subset_valid
#print axioms MLTT.inhabitance_le_semanticInhabitance
#print axioms fol_valid
#print axioms pa_sentence
#print axioms pa_theorem
#print axioms pa_truth
#print axioms hol_typing
#print axioms mltt_inhabits
#print axioms mltt_fixed_type
#print axioms mltt_typing
#print axioms mltt_length_i64

end DaslLogicTest
