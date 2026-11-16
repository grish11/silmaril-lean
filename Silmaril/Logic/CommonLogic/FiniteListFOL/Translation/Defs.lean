module

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Thms
public import Silmaril.Logic.FirstOrder.Variables.Thms

/-! Structural translation of the entire admitted Core syntax into ordinary
public many-sorted FOL syntax. Variable substitutions make both binder kinds
independent of any chosen ordering of the ambient sorted context. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.FiniteListFOL
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder

abbrev Term (S : Core.Signature) {m : Nat} (Γ : Fin m → FiniteLists.ListSort)
    (s : FiniteLists.ListSort) := EQ.Term (FiniteLists.publicSignature (signature S)).toSignature Γ s

def kindSort : Core.Kind → FiniteLists.ListSort
  | .individual => .discourse
  | .reference => .reference
  | .sequence => .sequence

def weaken {S : Core.Signature} {m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    {s : FiniteLists.ListSort} (bound : FiniteLists.ListSort) (t : Term S Γ s) :
    Term S (Fin.cases bound Γ) s :=
  Variables.termRename Fin.succ (fun _ => rfl) t

/-- Computed reference heads are translated as terms, not reclassified as
fixed symbols or approximated by a family of named-head relations. -/
def translateTerm {S : Core.Signature} {n k m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence) :
    {a : Core.Kind} → Core.Expr S n k a → Term S Γ (kindSort a)
  | _, .var i => ρ i
  | _, .name d => .app (.extra (.discourse d)) (fun i => Fin.elim0 i)
  | _, .nonname r => .app (.extra (.nondiscourse r)) (fun i => Fin.elim0 i)
  | _, .lift t => .app (.extra .embed) (fun _ => translateTerm ρ σ t)
  | _, .app r xs => .app (.extra .apply)
      (Fin.cases (translateTerm ρ σ r) (fun _ => translateTerm ρ σ xs))
  | _, .nil => .app .nil (fun i => Fin.elim0 i)
  | _, .cons x xs => .app .cons
      (Fin.cases (translateTerm ρ σ x) (fun _ => translateTerm ρ σ xs))
  | _, .marker m => .app (.extra (.marker m)) (fun i => Fin.elim0 i)
  | _, .seqvar i => σ i
  | _, .append xs ys => .app (.extra .append)
      (Fin.cases (translateTerm ρ σ xs) (fun _ => translateTerm ρ σ ys))

/-- Every Core connective and both binders compile into the full FOL language.
A sequence binder quantifies over the entire designated list carrier. -/
def translateFormula {S : Core.Signature} : {n k m : Nat} →
    {Γ : Fin m → FiniteLists.ListSort} →
    (Fin n → Term S Γ .discourse) → (Fin k → Term S Γ .sequence) →
    Core.Formula S n k → FOL.Formula (FiniteLists.publicSignature (signature S)) Γ
  | _, _, _, _, ρ, σ, .equal t u => .eq (translateTerm ρ σ t) (translateTerm ρ σ u)
  | _, _, _, _, ρ, σ, .pred r xs => .rel Rel.holds
      (Fin.cases (translateTerm ρ σ r) (fun _ => translateTerm ρ σ xs))
  | _, _, _, _, _, _, .tt => .tt
  | _, _, _, _, _, _, .ff => .not .tt
  | _, _, _, _, ρ, σ, .neg p => .not (translateFormula ρ σ p)
  | _, _, _, _, ρ, σ, .conj p q => .and (translateFormula ρ σ p) (translateFormula ρ σ q)
  | _, _, _, _, ρ, σ, .disj p q =>
      .not (.and (.not (translateFormula ρ σ p)) (.not (translateFormula ρ σ q)))
  | _, _, _, _, ρ, σ, .impl p q =>
      .not (.and (translateFormula ρ σ p) (.not (translateFormula ρ σ q)))
  | _, _, _, _, ρ, σ, .iff p q =>
      .and (.not (.and (translateFormula ρ σ p) (.not (translateFormula ρ σ q))))
        (.not (.and (translateFormula ρ σ q) (.not (translateFormula ρ σ p))))
  | _, _, _, Γ, ρ, σ, .all p =>
      .all (Variables.consTail (Sg := FiniteLists.publicSignature (signature S)) .discourse Γ)
        (translateFormula
          (Fin.cases (.var 0) (fun i => weaken .discourse (ρ i)))
          (fun i => weaken .discourse (σ i)) p)
  | _, _, _, _, ρ, σ, .ex p =>
      Variables.existsFormula (Sg := FiniteLists.publicSignature (signature S)) .discourse
        (translateFormula
          (Fin.cases (.var 0) (fun i => weaken .discourse (ρ i)))
          (fun i => weaken .discourse (σ i)) p)
  | _, _, _, Γ, ρ, σ, .allSeq p =>
      .all (Variables.consTail (Sg := FiniteLists.publicSignature (signature S)) .sequence Γ)
        (translateFormula
          (fun i => weaken .sequence (ρ i))
          (Fin.cases (.var 0) (fun i => weaken .sequence (σ i))) p)
  | _, _, _, _, ρ, σ, .exSeq p =>
      Variables.existsFormula (Sg := FiniteLists.publicSignature (signature S)) .sequence
        (translateFormula
          (fun i => weaken .sequence (ρ i))
          (Fin.cases (.var 0) (fun i => weaken .sequence (σ i))) p)

def sentence {S : Core.Signature} (p : Core.Sentence S) :
    FOL.Sentence (FiniteLists.publicSignature (signature S)) :=
  ⟨Fin.elim0, translateFormula Fin.elim0 Fin.elim0 p⟩

/-- Semantic encoding is identity on the two base universes and the actual
list-evaluation equivalence on the sequence universe. -/
noncomputable def encodeValue {S : Core.Signature} (M : Model S) :
    (a : Core.Kind) → Core.Value (decode M) a → M.obj.obj.carrier (kindSort a)
  | .individual, x => x
  | .reference, r => r
  | .sequence, xs => FiniteLists.evaluationEquiv M.obj xs

/-- Satisfiability in the entire independent target model category. The input
may contain any target FOL sentences, not only translated Core sentences. -/
def TargetSat {S : Core.Signature} (H : Set (room S).Sen) : Prop :=
  ∃ M : Model S, ∀ p ∈ H, (room S).Sat M p

/-- Unsatisfiability among all admitted independent target models. -/
def TargetUnsat {S : Core.Signature} (H : Set (room S).Sen) : Prop := ¬ TargetSat H

end Silmaril.Logic.CommonLogic.FiniteListFOL
