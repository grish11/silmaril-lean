module

public import Silmaril.Logic.Matching.GuardedFOL.Thms
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

inductive Relation : (n : Nat) → (Fin n → Unit) → Type where
  | edge : Relation 2 (fun _ => ())
  | flag : Relation 0 (fun _ => ())

abbrev relational : FOL.Signature where
  S := Unit
  Op := fun _ _ _ => Empty
  Rel := Relation

abbrev relationalModel (A : Type) (E : A → A → Prop) (flag : Prop) : FOL.Structure relational where
  carrier _ := A
  op o := o.elim
  rel r args := match r with | .edge => E (args 0) (args 1) | .flag => flag

abbrev ctx (n : Nat) : Fin n → Unit := fun _ => ()

def universalTop : FOL.Sentence relational := ⟨ctx 0, .all (Δ := ctx 1) rfl .tt⟩
def existentialTop : FOL.Sentence relational := ⟨ctx 0, .not (.all (Δ := ctx 1) rfl (.not .tt))⟩
def nullaryFlag : FOL.Sentence relational := ⟨ctx 0, .rel .flag (fun i => i.elim0)⟩

/-- A native point check in the canonical Unit truth carrier. -/
theorem expanded_point (M : FOL.Structure relational) (p : FOL.Sentence relational) :
    () ∈ (expand M).base.denote (fun i => i.elim0) (formula p.formula) ↔ p.Holds M := by
  rw [← expanded_satisfaction M p]
  constructor
  · intro hp v w
    have hv : v = (fun i => i.elim0) := funext (fun i => i.elim0)
    have hw : w = () := Subsingleton.elim _ _
    subst v; subst w
    exact hp
  · intro hp
    exact hp _ ()

/-- The padded None exists, but the guarded universal stays vacuously true. -/
theorem empty_universal_native :
    () ∈ (expand (relationalModel Empty (fun _ _ => False) False)).base.denote
      (fun i => i.elim0) (formula universalTop.formula) :=
  (expanded_point _ universalTop).mpr (fun _ _ => trivial)

/-- Padding does not turn the empty source existential into a true formula. -/
theorem empty_existential_native :
    () ∉ (expand (relationalModel Empty (fun _ _ => False) False)).base.denote
      (fun i => i.elim0) (formula existentialTop.formula) := by
  intro h
  have hs := (expanded_point _ existentialTop).mp h
  exact hs (fun θ _ => (θ 0).elim)

/-- Nullary relations retain truth even when every source object sort is empty. -/
theorem empty_nullary_true :
    () ∈ (expand (relationalModel Empty (fun _ _ => False) True)).base.denote
      (fun i => i.elim0) (formula nullaryFlag.formula) :=
  (expanded_point _ nullaryFlag).mpr trivial

theorem empty_nullary_false :
    () ∉ (expand (relationalModel Empty (fun _ _ => False) False)).base.denote
      (fun i => i.elim0) (formula nullaryFlag.formula) :=
  fun h => (expanded_point _ nullaryFlag).mp h

/-- Nested quantification preserves the saved outer variable. -/
def savedOuter : FOL.Sentence relational := ⟨ctx 0,
  .all (Δ := ctx 1) rfl (.not (.all (Δ := ctx 2) rfl (.not (.eq (.var 0) (.var 1)))))⟩

theorem savedOuter_native (A : Type) (E : A → A → Prop) :
    () ∈ (expand (relationalModel A E False)).base.denote
      (fun i => i.elim0) (formula savedOuter.formula) := by
  apply (expanded_point _ savedOuter).mpr
  intro θ _ h
  apply h (show (∀ i, (relationalModel A E False).carrier ((ctx 2) i)) from Fin.cases (θ 0) θ)
  · intro _; rfl
  · rfl

inductive Function : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | zero : Function 0 (fun _ => ()) ()
  | succ : Function 1 (fun _ => ()) ()

abbrev functional : FOL.Signature where
  S := Unit
  Op := Function
  Rel := fun _ _ => Empty

abbrev naturals : FOL.Structure functional where
  carrier _ := Nat
  op o args := match o with | .zero => 0 | .succ => args 0 + 1
  rel r := r.elim

def zeroTerm : EQ.Term functional.toSignature (ctx 0) () := .app .zero (fun i => i.elim0)
def successorZero : EQ.Term functional.toSignature (ctx 0) () := .app .succ (fun _ => zeroTerm)

theorem singleton_function_native :
    (expand naturals).base.denote (fun i => i.elim0) (term successorZero) = {some 1} := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨values, hv, other, ho, hy⟩
    have hzero : values 0 = some 0 := by
      rcases hv 0 with ⟨_, _, h⟩
      rcases h with ⟨_, _, hy⟩
      exact hy
    have hother : other 0 = 0 := Option.some.inj ((ho 0).symm.trans hzero)
    exact hy.trans (congrArg some (congrArg (· + 1) hother))
  · intro hy
    refine ⟨fun _ => some 0, ?_, fun _ => 0, fun _ => rfl, hy⟩
    intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, rfl⟩

/-- A raw empty graph for a source constant cannot satisfy the singleton law. -/
abbrev missingConstant : FirstOrder.Model (signature functional).symbols where
  carrier _ := Unit
  nonempty _ := ⟨()⟩
  operation op _ := match op with
    | .function _ => ∅
    | .relation r => r.elim
    | .active _ => Set.univ
    | .defined _ => Set.univ
    | .truth => Set.univ

theorem missingConstant_not_admitted (M : Model functional) : M.base ≠ missingConstant := by
  intro hbase
  obtain ⟨y, hy⟩ := M.function .zero (fun i => i.elim0)
  have hargs : (fun i : Fin 0 => (i.elim0 : (decode M).carrier ()).val) = (fun i => i.elim0) :=
    funext (fun i => i.elim0)
  rw [hargs] at hy
  let hasConstant := fun B : FirstOrder.Model (signature functional).symbols =>
    (B.operation (.function .zero) (fun i => i.elim0)).Nonempty
  have hm : hasConstant M.base := ⟨y.val, hy.symm ▸ Set.mem_singleton y.val⟩
  have impossible : hasConstant missingConstant := hbase ▸ hm
  exact impossible.elim (fun _ h => h)

/-- Partial truth-sort relations are excluded by actual raw graph constraints. -/
abbrev partialTruth : FirstOrder.Model (signature relational).symbols where
  carrier s := match s with | .object _ => Unit | .truth => Bool
  nonempty s := match s with | .object _ => ⟨()⟩ | .truth => ⟨false⟩
  operation op _ := match op with
    | .function o => o.elim
    | .relation _ => {false}
    | .active _ => Set.univ
    | .defined _ => Set.univ
    | .truth => Set.univ

theorem partialTruth_not_admitted (M : Model relational) : M.base ≠ partialTruth := by
  intro hbase
  let flagLaw := fun B : FirstOrder.Model (signature relational).symbols =>
    B.operation (.relation .flag) (fun i => i.elim0) = ∅ ∨
      B.operation (.relation .flag) (fun i => i.elim0) = Set.univ
  have hm : flagLaw M.base := M.relation .flag (fun i => i.elim0)
  have rawLaw : flagLaw partialTruth := hbase ▸ hm
  rcases rawLaw with he | hf
  · have bad : false ∈ (∅ : Set Bool) := he ▸ Set.mem_singleton false
    exact bad
  · change ({false} : Set Bool) = Set.univ at hf
    have bad : true ∈ ({false} : Set Bool) := hf.symm ▸ Set.mem_univ true
    exact Bool.false_ne_true bad.symm
end Silmaril.Logic.Matching.GuardedFOL.Examples

@[expose] public section
namespace Silmaril.Logic.Matching.GuardedFOL.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

abbrev boolModel := relationalModel Bool (fun a b => a = false ∧ b = true) False
abbrev boolEnv : (i : Fin 2) → (expand boolModel).base.carrier (.object ((ctx 2) i)) :=
  ![some false, some true]

def forwardEdge : FOL.Formula relational (ctx 2) := .rel .edge ![.var 0, .var 1]
def reverseEdge : FOL.Formula relational (ctx 2) := .rel .edge ![.var 1, .var 0]

theorem binary_forward_native : () ∈ (expand boolModel).base.denote boolEnv (formula forwardEdge) := by
  refine ⟨![some false, some true], ?_, ![false, true], ?_, ⟨rfl, rfl⟩⟩
  · intro i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i
  · intro i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

theorem binary_reverse_native : () ∉ (expand boolModel).base.denote boolEnv (formula reverseEdge) := by
  rintro ⟨values, hv, other, ho, hedge⟩
  have hzero : values 0 = some true := hv 0
  have hother : other 0 = true := Option.some.inj ((ho 0).symm.trans hzero)
  exact Bool.false_ne_true (hedge.1.symm.trans hother)

inductive MixedRelation : (n : Nat) → (Fin n → Bool) → Type where
  | cross : MixedRelation 2 (Fin.cases false (fun _ => true))

abbrev mixed : FOL.Signature where
  S := Bool
  Op := fun _ _ _ => Empty
  Rel := MixedRelation

def collapse : mixed ⟶ relational where
  sorts _ := ()
  ops o := o.elim
  rels r := match r with | .cross => .edge

def mixedArgs : ∀ i, EQ.Term mixed.toSignature (Fin.cases true (fun _ : Fin 1 => false))
    (Fin.cases false (fun _ : Fin 1 => true) i) := Fin.cases (.var 1) (fun _ => .var 0)

def mixedSentence : FOL.Sentence mixed := ⟨fun _ => false,
  .all (Δ := fun _ : Fin 1 => false) rfl
    (.all (Δ := Fin.cases true (fun _ : Fin 1 => false)) rfl (.rel .cross mixedArgs))⟩

/-- Both guards and bound variable sorts commute with a noninjective sort map. -/
theorem mixed_sentence_naturality :
    SortMaps.Hom.sentence (signatureMap collapse) (sentence mixedSentence) =
      sentence (mixedSentence.map collapse) := sentence_map collapse mixedSentence

theorem mixed_decode_naturality :
    decode (reduct collapse (expand boolModel)) = (FOL.Structure.reduct collapse).obj (decode (expand boolModel)) :=
  decode_reduct collapse (expand boolModel)

/-- The separate truth sort also covers a source with no object sorts at all. -/
abbrev sortless : FOL.Signature where
  S := Empty
  Op := fun _ _ _ => Empty
  Rel := fun _ _ => Empty

abbrev sortlessModel : FOL.Structure sortless where
  carrier s := s.elim
  op o := o.elim
  rel r := r.elim

def sortlessTop : FOL.Sentence sortless := ⟨Fin.elim0, .tt⟩

theorem sortless_native :
    FirstOrder.Sentence.Satisfies (expand sortlessModel).base (sentence sortlessTop) :=
  (expanded_satisfaction sortlessModel sortlessTop).mpr trivial
end Silmaril.Logic.Matching.GuardedFOL.Examples

/-- info: 'Silmaril.Logic.Matching.GuardedFOL.formula_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.formula_denote
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.function_graph' depends on axioms: [Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.function_graph
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.decodeFunctor_naturality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.decodeFunctor_naturality
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.folNatural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.folNatural
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.folToGuardedMatching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.folToGuardedMatching
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.decodeExpansionIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.decodeExpansionIso
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.expanded_satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.expanded_satisfaction
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.fol_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.fol_sat_iff
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.fol_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.fol_unsat_iff
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.fol_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.fol_entails_iff
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.Examples.empty_existential_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.Examples.empty_existential_native
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.Examples.partialTruth_not_admitted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.Examples.partialTruth_not_admitted
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.Examples.singleton_function_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.Examples.singleton_function_native
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.Examples.mixed_sentence_naturality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.Examples.mixed_sentence_naturality
/-- info: 'Silmaril.Logic.Matching.GuardedFOL.Examples.sortless_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Matching.GuardedFOL.Examples.sortless_native
