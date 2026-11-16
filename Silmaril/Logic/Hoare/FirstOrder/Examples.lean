module

public import Silmaril.Logic.Hoare.FirstOrder.Institution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Hoare.FirstOrder.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- Empty symbols leave the carrier completely unrestricted, including the empty set. -/
def pure : FixedSignature Unit := ⟨fun _ _ _ => PEmpty, fun _ _ => PEmpty⟩

def pureModel (X : Type) : FOL.Structure pure.fol where
  carrier := fun _ => X
  op o := PEmpty.elim o
  rel r := PEmpty.elim r

def ctx (k : Nat) : Fin k → Unit := fun _ => ()

def allFalse : FOL.Sentence pure.fol := ⟨ctx 0, .all (Δ := ctx 1) rfl (.not .tt)⟩
def existsTrue : FOL.Sentence pure.fol := ⟨ctx 0, .not (.all (Δ := ctx 1) rfl (.not .tt))⟩
def reflexive : FOL.Sentence pure.fol := ⟨ctx 0, .all (Δ := ctx 1) rfl (.eq (.var 0) (.var 0))⟩
def collapse : FOL.Sentence pure.fol :=
  ⟨ctx 0, .all (Δ := ctx 1) rfl (.all (Δ := ctx 2) rfl (.eq (.var 0) (.var 1)))⟩

theorem empty_havoc (n : Nat) (h h' : Store (pureModel Empty)) :
    ¬ havoc (pureModel Empty) (n, ()) h h' := by
  rintro ⟨x,_⟩
  exact x.elim

theorem empty_allFalse : (sentence allFalse).Satisfies (Command Unit) (native (pureModel Empty)) := by
  apply (sentence_correct _ _).2
  intro ρ _
  exact (ρ 0).elim

theorem empty_not_existsTrue :
    ¬ (sentence existsTrue).Satisfies (Command Unit) (native (pureModel Empty)) := by
  intro h
  exact (sentence_correct _ _).1 h ((sentence_correct _ _).1 empty_allFalse)

theorem bool_not_collapse :
    ¬ (sentence collapse).Satisfies (Command Unit) (native (pureModel Bool)) := by
  intro h
  have hf := (sentence_correct _ _).1 h
  have he := hf (fun _ => false) (fun i => i.elim0)
    (Fin.cases true (fun _ => false)) (fun _ => HEq.rfl)
  exact Bool.noConfusion he

theorem reflexive_valid (X : Type) :
    (sentence reflexive).Satisfies (Command Unit) (native (pureModel X)) :=
  (sentence_correct _ _).2 (fun _ _ => rfl)

/-- Two open variables must read their own slots; unused slots may contain arbitrary data. -/
def twoValues : Store (pureModel Bool) := fun n =>
  if n = 0 then some ⟨(),false⟩ else if n = 1 then some ⟨(),true⟩ else some ⟨(),true⟩

theorem twoValues_encodes : Encodes (pureModel Bool) (ctx 2)
    (Fin.cases true (fun _ => false)) twoValues := by
  intro i
  fin_cases i <;> rfl

theorem open_equality_rejected :
    ¬ (compile (FOL.Formula.eq (Γ := ctx 2) (.var 0) (.var 1))).Holds
      (native (pureModel Bool)) twoValues := by
  rw [compile_correct _ _ _ _ twoValues_encodes]
  exact Bool.noConfusion

theorem unused_store_closed :
    (compile reflexive.formula).Holds (native (pureModel Bool)) twoValues :=
  (closed_correct _ _ _).2 (fun _ _ => rfl)

/-- Reusing slot zero for both quantifiers is observably wrong for this compiler. -/
def badBinders : PDL.Formula (language pure.fol) :=
  .box (.action (0, ())) (.box (.action (0, ()))
    (.atom (.eq (ctx 2) (.var 0) (.var 0))))

def nestedReflexive : FOL.Sentence pure.fol :=
  ⟨ctx 0, .all (Δ := ctx 1) rfl (.all (Δ := ctx 2) rfl (.eq (.var 0) (.var 0)))⟩

theorem nested_reflexive_valid :
    (sentence nestedReflexive).Satisfies (Command Unit) (native (pureModel Bool)) :=
  (sentence_correct _ _).2 (fun _ _ _ _ => rfl)

/-- At the empty store the first variable's required slot one is absent. -/
theorem badBinders_rejected : ¬ badBinders.Holds (native (pureModel Bool)) (empty _) := by
  intro h
  have hb := h _ ⟨false,rfl⟩ _ ⟨true,rfl⟩
  obtain ⟨ρ,hh,_⟩ := hb
  have he := hh (0 : Fin 2)
  simp [slot, empty, Function.update_of_ne] at he

/-- A native model whose arbitrary valuation violates actual FOL equality. -/
def badNative : PDL.Model (language pure.fol) :=
  ⟨Unit, fun _ _ _ => True, fun _ => ∅, ()⟩

theorem unrestricted_reflexive_failure :
    ¬ (sentence reflexive).Satisfies (Command Unit) badNative := by
  intro h
  exact h () not_false () ⟨rfl,not_false⟩ () trivial

/-- The canonical target retains a genuinely noninjective source model arrow. -/
def squash : FOL.Structure.Hom (pureModel Bool) (pureModel Unit) where
  map _ _ := ()
  map_op o := PEmpty.elim o
  map_rel r := PEmpty.elim r

theorem squash_not_injective : ¬ Function.Injective (squash.map ()) := by
  intro h
  exact Bool.noConfusion (h (show squash.map () false = squash.map () true from rfl))

theorem actual_model_arrow : (forgetModels pure).map squash = squash := rfl

inductive SourceOp : (n : Nat) → (Fin n → Unit) → Unit → Type
  | left : SourceOp 0 (fun _ => ()) ()
  | right : SourceOp 0 (fun _ => ()) ()

inductive TargetOp : (n : Nat) → (Fin n → Unit) → Unit → Type
  | only : TargetOp 0 (fun _ => ()) ()

def source : FixedSignature Unit := ⟨SourceOp, fun _ _ => PEmpty⟩
def target : FixedSignature Unit := ⟨TargetOp, fun _ _ => PEmpty⟩
def symbolsCollapse : source ⟶ target :=
  ⟨fun o => match o with | .left => .only | .right => .only, fun r => PEmpty.elim r⟩

theorem symbolsCollapse_noninjective :
    symbolsCollapse.operations SourceOp.left = symbolsCollapse.operations SourceOp.right ∧
      SourceOp.left ≠ SourceOp.right := ⟨rfl, by intro h; cases h⟩

def separated : FOL.Structure source.fol where
  carrier := fun _ => Bool
  op o _ := match o with | .left => false | .right => true
  rel r := PEmpty.elim r

def collapsed : FOL.Structure target.fol where
  carrier := fun _ => Bool
  op o _ := match o with | .only => false
  rel r := PEmpty.elim r

def constantsEqual : FOL.Sentence source.fol :=
  ⟨ctx 0, .eq (.app .left (fun j => j.elim0)) (.app .right (fun j => j.elim0))⟩

theorem separated_rejected : ¬ (sentence constantsEqual).Satisfies (Command Unit) (native separated) := by
  intro h
  exact Bool.noConfusion ((sentence_correct _ _).1 h)

theorem collapsed_accepted :
    (sentence (constantsEqual.map symbolsCollapse.fol)).Satisfies (Command Unit) (native collapsed) :=
  (sentence_correct _ _).2 rfl

theorem actual_reduct_square :
    native ((FOL.Structure.reduct symbolsCollapse.fol).obj collapsed) =
      ModalMu.reduct (languageMap symbolsCollapse) (native collapsed) :=
  native_reduct symbolsCollapse collapsed

/-- Sort collapse is deliberately absent: every admitted map fixes each sort. -/
theorem admitted_sorts_fixed (S : Type) {A B : FixedSignature S} (f : A ⟶ B) :
    f.fol.sorts = id := rfl

inductive Predicate : (n : Nat) → (Fin n → Unit) → Type
  | chosen : Predicate 1 (fun _ => ())

def relational : FixedSignature Unit := ⟨fun _ _ _ => PEmpty, Predicate⟩

def relationalModel : FOL.Structure relational.fol where
  carrier := fun _ => Bool
  op o := PEmpty.elim o
  rel r args := match r with | .chosen => args 0 = true

def chosenVariable : FOL.Formula relational.fol (ctx 1) :=
  .rel .chosen (fun _ => .var 0)

theorem actual_relation_observation :
    (compile chosenVariable).Holds (native relationalModel) (fun _ => some ⟨(),true⟩) := by
  exact (compile_correct relationalModel chosenVariable (fun _ => true) _ (fun _ => rfl)).2 rfl

theorem actual_relation_rejected :
    ¬ (compile chosenVariable).Holds (native relationalModel) (fun _ => some ⟨(),false⟩) := by
  rw [compile_correct _ _ (fun _ => false) _ (fun _ => rfl)]
  exact Bool.noConfusion

/-- A real havoc command can invalidate an open equality precondition. -/
def openEquality : FOL.Formula pure.fol (ctx 2) := .eq (.var 0) (.var 1)

def sameVariables : PDL.Formula (language pure.fol) := compile openEquality

def havocEquality : Hoare.Triple (Command Unit) (signature pure.fol) :=
  ⟨some (0,()), sameVariables, sameVariables⟩

theorem havoc_does_not_preserve_equality :
    ¬ havocEquality.Satisfies (Command Unit) (native (pureModel Bool)) := by
  intro h
  let before : Store (pureModel Bool) := fun _ => some ⟨(),true⟩
  have hb : sameVariables.Holds (native (pureModel Bool)) before :=
    (compile_correct (pureModel Bool) openEquality
      (fun _ => true) before (fun _ => rfl)).2 rfl
  have ha := h before hb (Function.update before 0 (some ⟨(),false⟩)) ⟨false,rfl⟩
  have he := (compile_correct _ _ (Fin.cases true (fun _ => false)) _ (by
    intro i
    fin_cases i <;> rfl)).1 ha
  exact Bool.noConfusion he

end Silmaril.Logic.Hoare.FirstOrder.Examples
