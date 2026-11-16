module

public import Silmaril.Logic.CommonLogic.FirstOrder.Expansion

@[expose] public section

namespace Silmaril.Logic.CommonLogic.FirstOrder.Examples

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

inductive Operation : Nat → Type where
  | a : Operation 0
  | f : Operation 1
  | g : Operation 1

inductive Predicate : Nat → Type where
  | p : Predicate 1
  | q : Predicate 0

def signature : Signature := ⟨Operation, Predicate⟩

abbrev arithmetic : FOL.Structure (publicSignature signature) where
  carrier _ := Nat
  op := fun {_ _ _} o args => match o with
    | .a => 0
    | .f => args 0 + 1
    | .g => args 0 + 2
  rel := fun {_ _} r args => match r with
    | .p => args 0 = 1
    | .q => True

def a {n : Nat} {Γ : Fin n → Unit} : EQ.Term (publicSignature signature).toSignature Γ () :=
  .app (w := fun _ => ()) .a Fin.elim0

def fa {n : Nat} {Γ : Fin n → Unit} : EQ.Term (publicSignature signature).toSignature Γ () :=
  .app .f (fun _ => a)

/-- The elementary client P(f(a)), with a=0, f(x)=x+1, and P(x) meaning x=1. -/
def pfa : FOL.Sentence (publicSignature signature) :=
  ⟨Fin.elim0, .rel .p (fun _ => fa)⟩

def nullaryPredicate : FOL.Sentence (publicSignature signature) :=
  ⟨Fin.elim0, .rel (w := fun _ => ()) .q Fin.elim0⟩

theorem pfa_true : pfa.Holds arithmetic := rfl

theorem translated_pfa_true :
    (Core.room (clSignature signature)).Sat (expand arithmetic 0) (sentence pfa) := by
  apply (sentence_holds _ pfa).mp
  rw [decode_expand]
  exact pfa_true

theorem translated_nullary_true :
    (Core.room (clSignature signature)).Sat
      (expand arithmetic 0) (sentence nullaryPredicate) := by
  apply (sentence_holds _ nullaryPredicate).mp
  rw [decode_expand]
  trivial

/-- Arity-preserving symbol maps may identify the distinct unary symbols f and g. -/
def collapse : signature ⟶ signature where
  ops _ o := match o with
    | .a => .a
    | .f => .f
    | .g => .f
  rels _ r := r

theorem collapse_syntax : (sentence pfa).map (clMap collapse) =
    sentence (pfa.map (publicMap collapse)) := sentence_map collapse pfa

abbrev singletonModel : FOL.Structure (publicSignature signature) where
  carrier _ := Unit
  op := fun {_ _ _} _ _ => ()
  rel := fun {_ _} _ _ => True

/-- A genuine noninjective public model homomorphism is retained in the nonempty source. -/
def collapseModel : arithmetic ⟶ singletonModel where
  map _ _ := ()
  map_op _ _ := rfl
  map_rel _ _ _ := trivial

def nonemptyCollapse : (⟨arithmetic, ⟨0⟩⟩ : NonemptyModel signature) ⟶
    (⟨singletonModel, ⟨()⟩⟩ : NonemptyModel signature) := ObjectProperty.homMk collapseModel

theorem collapseModel_not_injective : ¬ Function.Injective (collapseModel.map ()) := by
  intro h
  have hn : (0 : Nat) = 1 := h rfl
  exact Nat.zero_ne_one hn

/-- No operations or relations: its public FOL model may have an empty carrier. -/
def emptySignature : Signature := ⟨fun _ => Empty, fun _ => Empty⟩

abbrev emptyModel : FOL.Structure (publicSignature emptySignature) where
  carrier _ := Empty
  op := fun {_ _ _} o => Empty.elim o
  rel := fun {_ _} r => Empty.elim r

/-- ∃x, x=x, expressed in public FOL's primitive connectives. -/
def existsIndividual : FOL.Sentence (publicSignature emptySignature) :=
  ⟨Fin.elim0, .not (.all (Δ := fun _ => ()) rfl (.not (.eq (.var 0) (.var 0))))⟩

theorem empty_no_expansion :
    ¬ ∃ N : Core.Model (clSignature emptySignature), decode N = emptyModel := by
  rw [exists_expansion_iff]
  exact not_nonempty_iff.mpr inferInstance

theorem empty_not_exists : ¬ existsIndividual.Holds emptyModel := by
  intro h
  apply h
  intro ρ _
  exact Empty.elim (ρ 0)

theorem every_cl_exists (N : Core.Model (clSignature emptySignature)) :
    (Core.room (clSignature emptySignature)).Sat N (sentence existsIndividual) := by
  apply (sentence_holds N existsIndividual).mp
  intro h
  obtain ⟨x⟩ := N.nonempty
  exact h (fun _ => x) (fun i => Fin.elim0 i) rfl

/-- The unrestricted comorphism cannot reflect consequence: CL has an individual,
but the actual empty public FOL model refutes its existence. -/
theorem unrestricted_reflection_fails :
    ¬ ((institution.obj emptySignature).Entails ∅ existsIndividual) ∧
      (Core.room (clSignature emptySignature)).Entails
        (sentence '' (∅ : Set (FOL.Sentence (publicSignature emptySignature)))) (sentence existsIndividual) := by
  constructor
  · intro h
    exact empty_not_exists (h emptyModel (fun _ hp => False.elim hp))
  · intro N _
    exact every_cl_exists N

theorem empty_heads_elim (h : Heads emptySignature) : False := by
  rcases h with (⟨n,o⟩ | ⟨n,r⟩)
  · exact Empty.elim o
  · exact Empty.elim r

/-- Small full CL models still have extensions on unnamed individual references. -/
abbrev constantCL (D : Type) (d : D) : Core.Model (clSignature emptySignature) where
  Reference := D
  Discourse := D
  nonempty := ⟨d⟩
  embed := id
  injective := Function.injective_id
  discourse := Empty.elim
  nondiscourse h := False.elim (empty_heads_elim h)
  outside h _ := False.elim (empty_heads_elim h)
  sequence := Empty.elim
  function _ _ := d
  relation _ _ := False

/-- An actual CL homomorphism with a noninjective discourse map. -/
def constantCLCollapse : constantCL Nat 0 ⟶ constantCL Unit () where
  reference _ := ()
  discourse _ := ()
  embed _ := rfl
  name x := Empty.elim x
  nonname h := False.elim (empty_heads_elim h)
  sequence x := Empty.elim x
  function _ _ := rfl
  relation _ _ h := False.elim h

theorem decoder_keeps_noninjective :
    ¬ Function.Injective ((models emptySignature).map constantCLCollapse |>.map ()) := by
  intro h
  have hn : (0 : Nat) = 1 := h rfl
  exact Nat.zero_ne_one hn

/-- Empty-signature public FOL sees no CL operation extensions. -/
def forgottenIdentity : decode (constantCL Bool false) ⟶ decode (constantCL Bool true) where
  map _ := id
  map_op o _ := Empty.elim o
  map_rel r _ := Empty.elim r

/-- The decoder is not full: this actual public FOL homomorphism cannot lift to a CL homomorphism. -/
theorem forgottenIdentity_no_lift :
    ¬ ∃ h : constantCL Bool false ⟶ constantCL Bool true, decodeHom h = forgottenIdentity := by
  rintro ⟨h,hh⟩
  have hf : h.discourse false = false := congrArg (fun k => k.map () false) hh
  have ho : h.discourse false = true := h.function false []
  rw [hf] at ho
  cases ho

end Silmaril.Logic.CommonLogic.FirstOrder.Examples
