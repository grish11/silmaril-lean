module

public import Silmaril.Logic.Algebraic.OrderSorted.Thms
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Fin

/-! A bounded ELF-style relocation toy. Byte, word and address are 8, 16 and
32 bits. Addition wraps modulo 2^32; no claim about a specific ELF ABI is made. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Examples
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

abbrev Sorts := Fin 3
abbrev byte : Sorts := 0
abbrev word : Sorts := 1
abbrev address : Sorts := 2

def bound (s : Sorts) : Nat := if s = byte then 256 else if s = word then 65536 else 4294967296

theorem bound_monotone : Monotone bound := by
  intro s t h
  fin_cases s <;> fin_cases t <;> norm_num [bound, byte, word] at *

inductive Op : (n : Nat) → (Fin n → Sorts) → Sorts → Type where
  | byteLiteral (x : Fin 256) : Op 0 (fun i => i.elim0) byte
  | addressAdd : Op 2 (fun _ => address) address

abbrev signature : Signature := ⟨⟨Sorts, Op⟩, inferInstance⟩

/-- Exact widening, not an identification of the three carrier types. -/
def zeroExtend {s t : Sorts} (h : s ≤ t) (x : Fin (bound s)) : Fin (bound t) :=
  Fin.castLE (bound_monotone h) x

abbrev algebra : Algebra signature where
  carrier s := Fin (bound s)
  op o args := match o with
    | .base (.byteLiteral x) => x
    | .base .addressAdd => args 0 + args 1
    | .inclusion _ _ h => zeroExtend h (args 0)

abbrev model : Model signature where
  algebra := algebra
  coherent := {
    identity := fun _ _ => Fin.ext rfl
    injective := by
      intro s t h x y he
      exact Fin.ext (congrArg (fun z : Fin (bound t) => z.val) he)
    composition := fun _ _ _ => Fin.ext rfl }

/-- Direct byte-to-address widening agrees with the route through word. -/
theorem byte_word_address (x : Fin (bound byte)) :
    zeroExtend (show byte ≤ address by decide) x =
      zeroExtend (show word ≤ address by decide) (zeroExtend (show byte ≤ word by decide) x) :=
  Fin.ext rfl

abbrev context : Fin 2 → Sorts := Fin.cases address (fun _ => byte)
abbrev Term (s : Sorts) := EQ.Term (compiled signature) context s

def widen {s t : Sorts} (h : s ≤ t) (x : Term s) : Term t :=
  EQ.Term.app (Sg := compiled signature) (Operation.inclusion (A := signature) s t h) (fun _ => x)

def directAddend : Term address := widen (by decide : byte ≤ address) (.var 1)
def stagedAddend : Term address :=
  widen (by decide : word ≤ address) (widen (by decide : byte ≤ word) (.var 1))

def relocation (addend : Term address) : Term address :=
  EQ.Term.app (.base .addressAdd) (Fin.cases (.var 0) (fun _ => addend))

def assignment (base : Fin (bound address)) (addend : Fin (bound byte)) :
    (i : Fin 2) → algebra.carrier (context i) := Fin.cases base (fun _ => addend)

/-- Independent arithmetic client for the toy's base-plus-addend expression. -/
def relocate (base : Fin (bound address)) (addend : Fin (bound byte)) : Fin (bound address) :=
  base + zeroExtend (by decide : byte ≤ address) addend

/-- The translation target is the actual public EQ evaluator, not a placeholder. -/
theorem eval_relocation (base : Fin (bound address)) (addend : Fin (bound byte)) :
    (relocation directAddend).eval algebra (assignment base addend) = relocate base addend := rfl

theorem eval_staged_relocation (base : Fin (bound address)) (addend : Fin (bound byte)) :
    (relocation stagedAddend).eval algebra (assignment base addend) = relocate base addend := by
  change base + zeroExtend (show word ≤ address by decide)
    (zeroExtend (show byte ≤ word by decide) addend) =
      base + zeroExtend (show byte ≤ address by decide) addend
  exact congrArg (fun x => base + x) (byte_word_address addend).symm

abbrev coherenceEquation : Sentence signature :=
  ⟨2, context, address, relocation directAddend, relocation stagedAddend⟩

/-- Path coherence holds for every coherent model, not just the numeric toy. -/
theorem coherence_valid (M : Model signature) : Satisfies M coherenceEquation := by
  intro v
  apply congrArg (M.algebra.op (.base .addressAdd))
  funext i
  fin_cases i
  · rfl
  · exact (M.coherent.composition _ _ (v 1)).symm

theorem relocation_4096_255 :
    (relocation stagedAddend).eval algebra (assignment ⟨4096, by decide⟩ ⟨255, by decide⟩) =
      ⟨4351, by decide⟩ := by decide

/-- A concrete nonempty satisfying model. -/
theorem satisfiable : ∃ M : Model signature,
    Nonempty (M.algebra.carrier byte) ∧ Satisfies M coherenceEquation :=
  ⟨model, ⟨⟨0, by decide⟩⟩, coherence_valid model⟩

abbrev falseEquation : Sentence signature :=
  ⟨1, fun _ => byte, byte, .var 0, .app (.base (.byteLiteral 0)) (fun i => i.elim0)⟩

theorem false_in_model : ¬ Satisfies model falseEquation := by
  intro h
  have bad := h (fun _ => (⟨1, by decide⟩ : Fin (bound byte)))
  exact (by decide : (1 : Nat) ≠ 0) (congrArg Fin.val bad)

/-- Removing the injection obligation would admit collapsed subsorts. -/
abbrev collapsed : Algebra signature where
  carrier _ := Nat
  op o args := match o with
    | .base (.byteLiteral x) => x.val
    | .base .addressAdd => args 0 + args 1
    | .inclusion _ _ _ => 0

theorem collapsed_not_coherent : ¬ Coherent collapsed := by
  intro h
  have bad := h.injective (show byte ≤ word by decide) (a₁ := 0) (a₂ := 1) rfl
  exact Nat.zero_ne_one bad

/-- Empty upper carriers force empty subsorts, independently of operation symbols. -/
theorem no_inhabited_subsort_of_empty {A : Signature} (M : Model A) {s t : A.base.S}
    (h : s ≤ t) [Nonempty (M.algebra.carrier s)] [IsEmpty (M.algebra.carrier t)] : False := by
  obtain ⟨x⟩ := ‹Nonempty (M.algebra.carrier s)›
  exact isEmptyElim (M.algebra.coerce h x)

abbrev emptySignature : Signature := ⟨⟨Sorts, fun _ _ _ => PEmpty⟩, inferInstance⟩

abbrev emptyModel : Model emptySignature where
  algebra := {
    carrier _ := PEmpty
    op := fun o args => match o with
      | .base o => o.elim
      | .inclusion _ _ _ => (args 0).elim }
  coherent := {
    identity := fun _ x => x.elim
    injective := fun _ x => x.elim
    composition := fun _ _ x => x.elim }

theorem empty_carriers_allowed (s : Sorts) : IsEmpty (emptyModel.algebra.carrier s) := inferInstance

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.satisfaction' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.satisfaction

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.fromEquational_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.fromEquational_modelExpansive

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.fromEquational_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.fromEquational_entails_iff

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Model.hom_coerce' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.Model.hom_coerce

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Examples.coherence_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.Examples.coherence_valid

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Examples.eval_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.Examples.eval_relocation

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Examples.eval_staged_relocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.Examples.eval_staged_relocation

/-- info: 'Silmaril.Logic.Algebraic.OrderSorted.Examples.collapsed_not_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.OrderSorted.Examples.collapsed_not_coherent

end Silmaril.Logic.Algebraic.OrderSorted.Examples
