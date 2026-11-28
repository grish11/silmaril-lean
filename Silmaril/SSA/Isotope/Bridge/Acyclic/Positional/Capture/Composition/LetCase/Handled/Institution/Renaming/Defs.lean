module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Defs
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetCase

/-! # Primitive renamings that keep the typed interface

A renaming is an instruction map into a finite structural signature. The
source signature is the target signature read through the map, so each
primitive keeps its argument and reply shapes by definition. Types, bound
contexts and results are not changed. This is narrower than the existing
signature maps, which may also change types.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Silmaril.Isotope.Institution.Acyclic.Captured (GrammarEquation RankedEquation mapGrammar mapRanked)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event)
open Free (Events)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- The source instructions of a renaming. Their signature is the target
signature read through the instruction map. -/
def Pulled {Φ Ψ : Type} (_ : Φ → Ψ) : Type := Φ

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] (r : Φ → Ψ)

instance : LetCase.Structural.Finite.Signature (Pulled r) where
  source f := LetCase.Structural.Finite.Signature.source (r f)
  target f := LetCase.Structural.Finite.Signature.target (r f)

/-- The instruction map on the pulled-back instructions. -/
def Pulled.map : Pulled r → Ψ := r

/-- Rename every primitive of an exact derivation. The bound context, the
result type and every intermediate type are unchanged. -/
def renameDerivation : {n : Nat} → {γ : Context n} → {t : LetCase.LocallyNameless.Tm Empty (Pulled r) n} → {A : Ty Empty} →
    Derivation (Pulled r) Γ₀ γ t A → Derivation Ψ Γ₀ γ (t.mapInstr (Pulled.map r)) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) ha => .op (f := r f) (renameDerivation ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (renameDerivation ha) (renameDerivation hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (renameDerivation ha) (renameDerivation hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (renameDerivation ha) (renameDerivation hb)
  | _, _, _, _, .inl ha => .inl (renameDerivation ha)
  | _, _, _, _, .inr hb => .inr (renameDerivation hb)
  | _, _, _, _, .case he hl hr => .case (renameDerivation he) (renameDerivation hl) (renameDerivation hr)
  | _, _, _, _, .abort ha => .abort (renameDerivation ha)

/-- Rename an operand. -/
def renameOperand {n : Nat} {γ : Context n} {A : Ty Empty} (a : Operand (Pulled r) γ A) : Operand Ψ γ A :=
  ⟨a.1.mapInstr (Pulled.map r), renameDerivation r a.2⟩

/-- Rename both sides of a typed LetCase equation at the same typing index. -/
def renameCase (e : CaseEquation (sig (Pulled r))) : CaseEquation (sig Ψ) :=
  ⟨e.1, renameOperand r e.2.1, renameOperand r e.2.2⟩

/-- The renaming as a relabelling of the existing instruction signatures.
Sources, targets and effects agree by definition. -/
def pulledHom : sig (Pulled r) ⟶ sig Ψ :=
  ⟨r, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- A relabelling of structural signatures keeps every type, so it keeps
products and the unit. The general instance is stated for abstract
instruction signatures and is not found at these concrete ones. -/
instance {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Φ] [LetCase.Structural.Finite.Signature Ψ]
    (f : sig Φ ⟶ sig Ψ) : f.toSignatureMap.PreservesProducts where
  unit := rfl
  product _ _ := rfl

instance {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Φ] [LetCase.Structural.Finite.Signature Ψ]
    (f : sig Φ ⟶ sig Ψ) : f.toSignatureMap.PreservesSums where
  empty := rfl
  coprod _ _ := rfl

/-- Rename a grammar sentence with the existing signature map of grammar
equations, at the relabelling. -/
def renameGrammar (e : GrammarEquation (sig (Pulled r))) : GrammarEquation (sig Ψ) :=
  mapGrammar (pulledHom r).toSignatureMap e

/-- Rename a ranked sentence with the existing signature map of ranked
equations, at the relabelling. -/
def renameRanked (e : RankedEquation (sig (Pulled r))) : RankedEquation (sig Ψ) :=
  mapRanked (pulledHom r).toSignatureMap e

/-- A request keeps its argument and is renamed with its primitive. -/
def renameRequest : Request (Events (Pulled r)) → Request (Events Ψ)
  | ⟨_, .call f argument⟩ => ⟨_, .call (r f) argument⟩

/-- The request map of a renaming. Replies are returned unchanged. -/
def renameEvents : (events (Pulled r)).toSignature ⟶ (events Ψ).toSignature where
  request := renameRequest r
  reply := fun ⟨_, .call _ _⟩ reply => reply

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
