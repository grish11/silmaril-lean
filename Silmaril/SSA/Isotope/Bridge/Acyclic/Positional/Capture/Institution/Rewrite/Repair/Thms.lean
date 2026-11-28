module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Soundness

/-! # Soundness of the new rule in the witnessed room -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open CategoryTheory CategoryTheory.Limits
open Isotope.LetCase.LocallyNameless (AbortCongr Derivation Tm)
open Isotope.LetCase.Semantics.Categorical (denote)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

/-- All derivations using only the new rule are derivations of the opt-in theory. -/
theorem SequencesEmpty.repaired {pe : ε} {e : GrammarEquation P} (h : SequencesEmpty e) : Repaired pe e :=
  AbortCongr.toAbortEquiv h

theorem Repaired.ofNative {pe : ε} {e : GrammarEquation P} (h : Derivable pe e) : Repaired pe e :=
  .equiv h

namespace EmptySequencing

/-- The exact #3817 packed witness performs the repair in its entry operand. -/
theorem sequencesEmpty (tail : List (Ty Empty)) : SequencesEmpty (equation tail) :=
  empties_witnessed_proof tail

theorem repaired (tail : List (Ty Empty)) : Repaired false (equation tail) :=
  (sequencesEmpty tail).repaired

end EmptySequencing

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] {J : V ⥤ C}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- Typed congruence instances of the repair preserve the Freyd denotation
at the supplied exact derivations. -/
theorem denote_sequencesEmpty [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty P.Instr n} {A : τ}
    {d : Derivation P.Instr Γ₀ β a A} {e : Derivation P.Instr Γ₀ β b A}
    (h : AbortCongr Γ₀ d e) : letI := I; denote J M d = denote J M e :=
  denote_sequencesEmpty_proof M I h

/-- The contextual repair is sound in every model of the existing room. -/
theorem SequencesEmpty.sat [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] {e : GrammarEquation P} (h : SequencesEmpty e)
    (B : (grammarRoom J P).Mod) : (grammarRoom J P).Sat B e :=
  sat_sequencesEmpty_proof B e h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
