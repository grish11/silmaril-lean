module

public import Silmaril.Logic.Matching.FirstOrder.Pointed.Defs
public import Silmaril.Logic.Institution.Examples.Propositional
public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.Tactic.Tauto

/-! An actual propositional comorphism into pointed matching. Atom symbols are
nullary set-valued operations, with unrestricted interpretations. Negation and
all Boolean connectives are interpreted at the chosen result. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.Pointed
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Algebraic.ManySorted (Signature)

/-- A one-sort signature containing only atom-labelled nullary operations. -/
inductive AtomOperation (P : Type) : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | atom (a : P) : AtomOperation P 0 Fin.elim0 ()

abbrev propositionalSignature (P : Type) : Signature Unit := ⟨AtomOperation P⟩

def propositionalSignatureMap {P Q : Type} (f : P → Q) :
    propositionalSignature P ⟶ propositionalSignature Q where
  operations op := match op with | .atom a => .atom (f a)

def propositionalSignatures : Type ⥤ Signature Unit where
  obj := propositionalSignature
  map f := propositionalSignatureMap f
  map_id _ := by
    apply Algebraic.ManySorted.Signature.Hom.ext
    intro n inputs output op
    cases op
    rfl
  map_comp f g := by
    apply Algebraic.ManySorted.Signature.Hom.ext
    intro n inputs output op
    cases op
    rfl

def encodePropositional {P : Type} : PL.Formula P → ClosedPattern () (propositionalSignature P)
  | .var a => .app (.atom a) (fun i => nomatch i)
  | .bot => Pattern.bottom
  | .imp p q => .neg (.conj (encodePropositional p) (.neg (encodePropositional q)))
  | .and p q => .conj (encodePropositional p) (encodePropositional q)
  | .or p q => .neg (.conj (.neg (encodePropositional p)) (.neg (encodePropositional q)))

/-- Every pointed target model gives a valuation, without a totality or
single-valuedness condition on its atom interpretations. -/
def pointValuation (P : Type) : Model () (propositionalSignature P) ⥤ PL.Model P where
  obj M := ULift.up (fun a => M.point ∈ M.base.operation (.atom a) (fun i => nomatch i))
  map h := ⟨fun a ha => by
    dsimp only [PL.Model.val] at ha ⊢
    have ht := h.base.operation (.atom a) (fun i => nomatch i) _ ha
    rw [h.point] at ht
    convert ht using 1
    congr 1
    funext i
    exact Fin.elim0 i⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem encodePropositional_satisfies {P : Type} (M : Model () (propositionalSignature P))
    (p : PL.Formula P) : M.Satisfies (encodePropositional p) ↔
      PL.Formula.eval ((pointValuation P).obj M).val p := by
  classical
  induction p with
  | var a =>
    exact Set.ext_iff.mp (FirstOrder.Model.denote_nullary M.base
      (fun i : Fin 0 => Fin.elim0 i) (.atom a)) M.point
  | bot =>
    change M.point ∈ M.base.denote _ Pattern.bottom ↔ False
    rw [FirstOrder.Model.denote_bottom]
    exact Iff.rfl
  | imp p q hp hq =>
    simp only [encodePropositional, Model.Satisfies, FirstOrder.Model.denote,
      Set.mem_compl_iff, Set.mem_inter_iff, PL.Formula.eval] at *
    tauto
  | and p q hp hq => exact and_congr hp hq
  | or p q hp hq =>
    simp only [encodePropositional, Model.Satisfies, FirstOrder.Model.denote,
      Set.mem_compl_iff, Set.mem_inter_iff, PL.Formula.eval] at *
    tauto

theorem encodePropositional_rename {P Q : Type} (f : P → Q) (p : PL.Formula P) :
    encodePropositional (p.rename f) = Pattern.map (propositionalSignatureMap f) (encodePropositional p) := by
  induction p with
  | var a =>
    change Pattern.app (A := propositionalSignature Q) (AtomOperation.atom (f a)) _ =
      Pattern.app (A := propositionalSignature Q) (AtomOperation.atom (f a)) _
    congr 1
    funext i
    exact Fin.elim0 i
  | bot => rfl
  | imp p q hp hq => simp only [PL.Formula.rename, encodePropositional, Pattern.map, hp, hq]
  | and p q hp hq => simp only [PL.Formula.rename, encodePropositional, Pattern.map, hp, hq]
  | or p q hp hq => simp only [PL.Formula.rename, encodePropositional, Pattern.map, hp, hq]

def propositionalCorridor (P : Type) : PL.room P ⟶ (institution ()).obj (propositionalSignature P) where
  sen := encodePropositional
  mod := pointValuation P
  sat := encodePropositional_satisfies

def propositionalNatural : PL.institution ⟶ propositionalSignatures ⋙ institution () where
  app := propositionalCorridor
  naturality := by
    intro P Q f
    exact Room.hom_ext (funext (encodePropositional_rename f)) rfl

/-- A shared Hets-compatible comorphism to pointwise, rather than global,
matching satisfaction; its reduct is defined on every target model. -/
def propositionalToPointedMatching : Inst.CoHom PL.inst ⟨Signature Unit, institution ()⟩ :=
  ⟨propositionalSignatures, propositionalNatural⟩

/-- Every propositional valuation is realized by a populated singleton target.
The unrestricted target also contains the multi-state models above. -/
def realizeValuation {P : Type} (v : P → Prop) : Model () (propositionalSignature P) where
  base :=
    { carrier := fun _ => Unit
      nonempty := fun _ => inferInstance
      operation := fun op => match op with | .atom a => fun _ => { _result : Unit | v a } }
  point := ()

theorem pointValuation_realize {P : Type} (v : PL.Model P) :
    (pointValuation P).obj (realizeValuation v.val) = v := by
  cases v
  rfl

/-- Every source model has a target expansion, enabling consequence borrowing. -/
theorem propositionalToPointedMatching_modelExpansive :
    propositionalToPointedMatching.ModelExpansive := by
  intro P v
  exact ⟨realizeValuation v.val, pointValuation_realize v⟩

/-- Global validity of an encoded formula means truth at every result's valuation. -/
theorem global_encodePropositional_iff {P : Type}
    (M : FirstOrder.Model (propositionalSignature P)) (p : PL.Formula P) :
    Sentence.Satisfies M (closedSentence () (encodePropositional p)) ↔
      ∀ point : M.carrier (), PL.Formula.eval ((pointValuation P).obj ⟨M, point⟩).val p := by
  rw [global_iff_all_points]
  exact forall_congr' (fun point => encodePropositional_satisfies ⟨M, point⟩ p)
end Silmaril.Logic.Matching.FirstOrder.Pointed
