module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Thms

/-! Original finite-coordinate controls. All examples are authored source
controls, and no build or solver observation is asserted by this module. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization

/-- a : 0, left : 1 → 0, right : 0 → 1. -/
def seeded : Profile where
  sortCount := 2
  operationCount := 3
  arity := Fin.cases 0 (Fin.cases 1 (Fin.cases 1 Fin.elim0))
  input := Fin.cases (fun i => i.elim0)
    (Fin.cases (fun _ => 1) (Fin.cases (fun _ => 0) (fun i => i.elim0)))
  output := Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0))

theorem left_operations :
    (operationsAt seeded (0 : Fin 2)).map Subtype.val = [(0 : Fin 3), (1 : Fin 3)] := by
  change @Eq (List (Fin 3)) ((operationsAt seeded (0 : Fin 2)).map Subtype.val) [0, 1]
  decide +kernel

theorem right_operations :
    (operationsAt seeded (1 : Fin 2)).map Subtype.val = [(2 : Fin 3)] := by
  change @Eq (List (Fin 3)) ((operationsAt seeded (1 : Fin 2)).map Subtype.val) [2]
  decide +kernel

def collapsedSignature : EQ.Signature := ⟨Unit, fun _ _ _ => Unit⟩

/-- Both sorts, and both unary operation symbols at their mapped profiles,
are actually identified in the ambient EQ signature. -/
def collapse : seeded.signature ⟶ collapsedSignature :=
  ⟨fun _ => (), fun _ => ()⟩

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  have bad : (0 : Fin 2) = 1 := h (show collapse.sorts (0 : Fin 2) = collapse.sorts (1 : Fin 2) from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) bad

theorem same_target_sort : coordinate collapse (0 : Fin 2) = coordinate collapse (1 : Fin 2) := rfl

theorem distinct_original_coordinates : (0 : Fin 2) ≠ 1 := by decide

/-- The ground range is at each ORIGINAL sort, not the range of a one-sort
replacement presentation after the ambient collapse. -/
theorem collapsed_ground_range (N : SignedSpectrum.NativeModel collapsedSignature)
    (i : Fin seeded.sortCount) :
    (generated collapse i).denote N.base (fun j => j.elim0) (fun j => j.elim0) =
      Set.range (fun t : Ground seeded.signature i =>
        (evaluate (reduct collapse N) t).val) :=
  generated_denote collapse N i

theorem original_equations_retained (E : Set (Equations seeded))
    (N : SignedSpectrum.NativeModel collapsedSignature) :
    Satisfies N (compiled E collapse) ↔
      Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Generated
        (reduct collapse N) ∧
        ExactGroundKernel (theory seeded E) (reduct collapse N) :=
  compiled_satisfaction E collapse N

/-- A real two-sort mutual cycle without nullary operations. -/
def unseeded : Profile where
  sortCount := 2
  operationCount := 2
  arity := fun _ => 1
  input := Fin.cases (fun _ => 1) (Fin.cases (fun _ => 0) Fin.elim0)
  output := Fin.cases 0 (Fin.cases 1 Fin.elim0)

theorem unseeded_no_ground {i : unseeded.signature.S}
    (t : Ground unseeded.signature i) : False := by
  induction t with
  | var j => exact j.elim0
  | @app n w s op args ih =>
      cases op with
      | mk c => exact ih (0 : Fin 1)

theorem unseeded_generated_empty {B : EQ.Signature} (σ : unseeded.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) (i : Fin unseeded.sortCount) :
    (generated σ i).denote N.base (fun j => j.elim0) (fun j => j.elim0) = ∅ := by
  rw [generated_denote]
  ext x
  constructor
  · rintro ⟨t, _⟩
    exact unseeded_no_ground t
  · exact False.elim

/-- Actual EQ carriers are empty at both sorts; total unary operations still
exist because each input tuple would contain an impossible argument. -/
def emptyAlgebra : EQ.Algebra unseeded.signature where
  carrier _ := Empty
  op := by
    intro n w s op args
    cases op with
    | mk c => exact (args (0 : Fin 1)).elim

def emptyNative : SignedSpectrum.NativeModel unseeded.signature :=
  GuardedFOL.expand (SignedSpectrum.structureOf emptyAlgebra)

theorem genuinely_empty_active (i : Fin unseeded.sortCount) :
    IsEmpty ((reduct (𝟙 unseeded.signature) emptyNative).carrier i) :=
  ⟨fun a => ((GuardedFOL.decodeExpansionIso
    (SignedSpectrum.structureOf emptyAlgebra)).hom.map i a).elim⟩

theorem padding_inhabited (i : Fin unseeded.sortCount) :
    Nonempty (emptyNative.base.carrier (coordinate (𝟙 unseeded.signature) i)) :=
  emptyNative.base.nonempty _

theorem empty_active_generated (i : Fin unseeded.sortCount) :
    (generated (𝟙 unseeded.signature) i).denote emptyNative.base
      (fun j => j.elim0) (fun j => j.elim0) = ∅ :=
  unseeded_generated_empty _ _ i

def noCoordinates : Profile where
  sortCount := 0
  operationCount := 0
  arity i := i.elim0
  input i := i.elim0
  output i := i.elim0

theorem no_invented_coordinate {B : EQ.Signature} (σ : noCoordinates.signature ⟶ B) :
    generated σ = (fun i => i.elim0) := by
  funext i
  exact i.elim0


/-- One ambient sort and one operation at each profile. Nullary symbols denote
zero; every positive-arity symbol denotes successor of its first argument. -/
def numericAmbient : EQ.Algebra collapsedSignature where
  carrier _ := Nat
  op := by
    intro n w s op args
    cases n with
    | zero => exact 0
    | succ n => exact Nat.succ (args 0)

abbrev numericSource := (EQ.Algebra.reduct collapse).obj numericAmbient
abbrev numericStructure := SignedSpectrum.structureOf numericAmbient

def numericNative : SignedSpectrum.NativeModel collapsedSignature :=
  GuardedFOL.expand numericStructure

theorem unary_symbols_identified :
    collapse.ops (Operation.mk (D := seeded) (1 : Fin 3)) =
      collapse.ops (Operation.mk (D := seeded) (2 : Fin 3)) := rfl

theorem both_unary_are_successor (x : Nat) :
    numericAmbient.op (collapse.ops (Operation.mk (D := seeded) (1 : Fin 3))) (fun _ => x) =
        Nat.succ x ∧
    numericAmbient.op (collapse.ops (Operation.mk (D := seeded) (2 : Fin 3))) (fun _ => x) =
        Nat.succ x := ⟨rfl, rfl⟩

/-- This invariant is proved by ORIGINAL sorted public ground-term induction.
The two unary source operations share an ambient interpretation, but alternate
the source output coordinate. No desired denotation predicate is supplied. -/
theorem numeric_evaluate_parity {i : seeded.signature.S}
    (t : Ground seeded.signature i) : (show Nat from evaluate numericSource t) % 2 = i.val := by
  induction t with
  | var j => exact j.elim0
  | @app n w s op args ih =>
      cases op with
      | mk c =>
          have hc : c = (0 : Fin 3) ∨ c = (1 : Fin 3) ∨ c = (2 : Fin 3) := by
            refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0))) c
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          rcases hc with rfl | rfl | rfl
          · rfl
          · have hh : (show Nat from evaluate numericSource (args (0 : Fin 1))) % 2 = 1 := ih (0 : Fin 1)
            change Nat.succ (evaluate numericSource (args (0 : Fin 1))) % 2 = 0
            have step : ∀ n : Nat, n % 2 = 1 → Nat.succ n % 2 = 0 := by
              intro n hn
              simp [Nat.succ_eq_add_one, Nat.add_mod, hn]
            exact step _ hh
          · have hh : (show Nat from evaluate numericSource (args (0 : Fin 1))) % 2 = 0 := ih (0 : Fin 1)
            change Nat.succ (evaluate numericSource (args (0 : Fin 1))) % 2 = 1
            have step : ∀ n : Nat, n % 2 = 0 → Nat.succ n % 2 = 1 := by
              intro n hn
              simp [Nat.succ_eq_add_one, Nat.add_mod, hn]
            exact step _ hh

/-- Decoding the actual native graph expansion commutes with original ground
evaluation. This is derived from unpad_op, not postulated model agreement. -/
theorem numeric_unpad_evaluate {i : seeded.signature.S}
    (t : Ground seeded.signature i) :
    GuardedFOL.unpad (evaluate (reduct collapse numericNative) t) =
      evaluate numericSource t := by
  induction t with
  | var j => exact j.elim0
  | @app n w s op args ih =>
      change GuardedFOL.unpad
        ((GuardedFOL.decode numericNative).op (collapse.ops op)
          (fun j => evaluate (reduct collapse numericNative) (args j))) =
        numericAmbient.op (collapse.ops op)
          (fun j => evaluate numericSource (args j))
      exact (GuardedFOL.unpad_op numericStructure (collapse.ops op)
        (fun j => evaluate (reduct collapse numericNative) (args j))).trans
          (congrArg (numericAmbient.op (collapse.ops op)) (funext ih))

theorem numeric_evaluate_raw {i : Fin seeded.sortCount}
    (t : Ground seeded.signature i) :
    (evaluate (reduct collapse numericNative) t).val =
      some (evaluate numericSource t) :=
  (GuardedFOL.unpad_spec (evaluate (reduct collapse numericNative) t)).symm.trans
    (congrArg some (numeric_unpad_evaluate t))

def zeroGround : Ground seeded.signature (0 : Fin 2) :=
  .app (Operation.mk (D := seeded) (0 : Fin 3)) (fun j => j.elim0)

def oneGround : Ground seeded.signature (1 : Fin 2) :=
  .app (Operation.mk (D := seeded) (2 : Fin 3)) (fun _ => zeroGround)

def twoGround : Ground seeded.signature (0 : Fin 2) :=
  .app (Operation.mk (D := seeded) (1 : Fin 3)) (fun _ => oneGround)

def threeGround : Ground seeded.signature (1 : Fin 2) :=
  .app (Operation.mk (D := seeded) (2 : Fin 3)) (fun _ => twoGround)

theorem zero_in_coordinate_zero :
    (some 0 : Option Nat) ∈ (generated collapse (0 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  apply Eq.mp (congrArg (fun S => (some 0 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (0 : Fin 2))).symm
  exact ⟨zeroGround, numeric_evaluate_raw zeroGround⟩

theorem one_in_coordinate_one :
    (some 1 : Option Nat) ∈ (generated collapse (1 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  apply Eq.mp (congrArg (fun S => (some 1 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (1 : Fin 2))).symm
  exact ⟨oneGround, numeric_evaluate_raw oneGround⟩

theorem two_in_coordinate_zero :
    (some 2 : Option Nat) ∈ (generated collapse (0 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  apply Eq.mp (congrArg (fun S => (some 2 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (0 : Fin 2))).symm
  exact ⟨twoGround, numeric_evaluate_raw twoGround⟩

theorem three_in_coordinate_one :
    (some 3 : Option Nat) ∈ (generated collapse (1 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  apply Eq.mp (congrArg (fun S => (some 3 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (1 : Fin 2))).symm
  exact ⟨threeGround, numeric_evaluate_raw threeGround⟩

theorem zero_not_in_coordinate_one :
    (some 0 : Option Nat) ∉ (generated collapse (1 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  intro hx
  have hx' := Eq.mp (congrArg (fun S => (some 0 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (1 : Fin 2))) hx
  obtain ⟨t, ht⟩ := hx'
  have he : (show Nat from evaluate numericSource t) = 0 :=
    Option.some.inj ((numeric_evaluate_raw t).symm.trans ht)
  have hp := numeric_evaluate_parity t
  have bad : (0 : Nat) = 1 :=
    (congrArg (fun n : Nat => n % 2) he).symm.trans hp
  exact Nat.zero_ne_one bad

theorem one_not_in_coordinate_zero :
    (some 1 : Option Nat) ∉ (generated collapse (0 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  intro hx
  have hx' := Eq.mp (congrArg (fun S => (some 1 : Option Nat) ∈ S)
    (generated_denote collapse numericNative (0 : Fin 2))) hx
  obtain ⟨t, ht⟩ := hx'
  have he : (show Nat from evaluate numericSource t) = 1 :=
    Option.some.inj ((numeric_evaluate_raw t).symm.trans ht)
  have hp := numeric_evaluate_parity t
  have bad : (1 : Nat) = 0 :=
    (congrArg (fun n : Nat => n % 2) he).symm.trans hp
  exact Nat.one_ne_zero bad

/-- Same actual target sort and same unary operation symbol, yet the two
compiled native patterns denote different subsets in the same actual model. -/
theorem collapsed_compiled_denotations_distinct :
    (generated collapse (0 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) ≠
    (generated collapse (1 : Fin 2)).denote numericNative.base
      (fun j => j.elim0) (fun j => j.elim0) := by
  intro h
  have hz := zero_in_coordinate_zero
  rw [h] at hz
  exact zero_not_in_coordinate_one hz

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples
