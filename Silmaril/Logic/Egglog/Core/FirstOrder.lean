module

public import Silmaril.Logic.Egglog.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

namespace Graph

inductive Relation (S : Signature) : (n : Nat) → (Fin n → S.S) → Type where
  | predicate {n w} (r : S.Rel n w) : Relation S n w
  /-- Column zero is the output. Keeping the full profile explicit makes sort
  translation commute with row formation without transporting dependent tuples. -/
  | row {n} {w : Fin (n+1) → S.S}
      (f : S.Function n (w ∘ Fin.succ) (w 0)) : Relation S (n+1) w

abbrev signature (S : Signature) : FOL.Signature :=
  ⟨S.toSignature, Relation S⟩

/-- A functional graph is the exact FOL interpretation of a partial dictionary. -/
def model {S : Signature} (M : Model S) : FOL.Structure (signature S) where
  toAlgebra := M.toAlgebra
  rel r := match r with
    | .predicate p => M.rel p
    | .row f => fun args => M.row f (fun i => args i.succ) (args 0)

def atom {S : Signature} {n : Nat} {Γ : Fin n → S.S} : Atom S Γ → FOL.Formula (signature S) Γ
  | .equal e => .eq e.lhs e.rhs
  | .relation r args => .rel (.predicate r) args
  | @Atom.row _ _ _ _ w s f args value =>
      .rel (.row (w := Fin.cases s w) f) (Fin.cases value args)

theorem atom_holds {S : Signature} {n : Nat} {Γ : Fin n → S.S} (M : Model S)
    (ρ : ∀ i, M.carrier (Γ i)) (a : Atom S Γ) :
    (atom a).Holds (model M) ρ ↔ a.Holds M ρ := by
  cases a <;> rfl

def conjunction {S : Signature} {n : Nat} {Γ : Fin n → S.S} :
    List (Atom S Γ) → FOL.Formula (signature S) Γ
  | [] => .tt
  | a :: rest => .and (atom a) (conjunction rest)

theorem conjunction_holds {S : Signature} {n : Nat} {Γ : Fin n → S.S} (M : Model S)
    (ρ : ∀ i, M.carrier (Γ i)) (as : List (Atom S Γ)) :
    (conjunction as).Holds (model M) ρ ↔ ∀ a ∈ as, a.Holds M ρ := by
  induction as with
  | nil =>
    constructor
    · intro _ a ha
      cases ha
    · intro _
      trivial
  | cons a rest ih =>
    change ((atom a).Holds (model M) ρ ∧ (conjunction rest).Holds (model M) ρ) ↔ _
    rw [atom_holds, ih]
    constructor
    · intro h b hb
      rcases List.mem_cons.mp hb with rfl | hm
      · exact h.1
      · exact h.2 b hm
    · intro h
      exact ⟨h a (.head _), fun b hb => h b (.tail _ hb)⟩

def sentence {S : Signature} : Sentence S → FOL.Sentence (signature S)
  | .rule r => EQtoFOL.closeAll r.context
      (.not (.and (conjunction r.body) (.not (atom r.head))))
  | .query q =>
      let closed := EQtoFOL.closeAll (Sg := signature S) q.context (.not (conjunction q.goals))
      ⟨closed.ctx,.not closed.formula⟩

theorem sentence_holds {S : Signature} (M : Model S) (s : Sentence S) :
    (sentence s).Holds (model M) ↔ s.Holds M := by
  cases s with
  | rule r =>
    rw [sentence, EQtoFOL.holds_closeAll]
    change (∀ ρ, ¬ ((conjunction r.body).Holds (model M) ρ ∧ ¬ (atom r.head).Holds (model M) ρ)) ↔ _
    simp only [not_and, not_not]
    exact forall_congr' (fun ρ => imp_congr (conjunction_holds M ρ r.body) (atom_holds M ρ r.head))
  | query q =>
    change (¬ (EQtoFOL.closeAll (Sg := signature S) q.context (.not (conjunction q.goals))).Holds (model M)) ↔ _
    rw [EQtoFOL.holds_closeAll]
    change (¬ ∀ ρ, ¬ (conjunction q.goals).Holds (model M) ρ) ↔ _
    rw [not_forall]
    apply exists_congr
    intro ρ
    exact not_not.trans (conjunction_holds M ρ q.goals)

/-- FOL in the functional-graph model class. This restriction is essential: arbitrary
FOL graph relations need not satisfy the input-to-output functional dependency. -/
def room (S : Signature) : Room.{0,0,1} :=
  ⟨FOL.Sentence (signature S), Cat.of (Model S), fun M p => p.Holds (model M)⟩

def corridor (S : Signature) : Core.room S ⟶ room S :=
  ⟨sentence, 𝟭 (Core.room S).Mod, sentence_holds⟩

theorem entails_iff (S : Signature) (H : Set (Sentence S)) (s : Sentence S) :
    (Core.room S).Entails H s ↔ (room S).Entails (sentence '' H) (sentence s) :=
  (corridor S).entails_map_iff (fun M => ⟨M,rfl⟩) H s

end Graph
end Silmaril.Logic.Egglog.Core
