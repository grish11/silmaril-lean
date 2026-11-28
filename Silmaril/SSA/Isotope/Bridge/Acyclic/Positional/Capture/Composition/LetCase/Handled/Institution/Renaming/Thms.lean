module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Sentence.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Comparison

/-! # The satisfaction condition for interface-preserving renamings

An injective renaming of primitives is a morphism of the existing
handled-trace signatures. The free tree of a renamed operand is the request
translation of the free tree of the original operand. With the existing
satisfaction condition of the handled-trace institution, a renamed directed
sentence holds in a model exactly when the original holds in its reduct.

Injectivity is what the existing trace signatures require of a request
map. The renamed LetCase sentence is built at the same typing index. It is
the sentence map of the existing LetCase institution at the relabelling,
and the existing type-changing sentence map at the relabelling. Grammar and
ranked sentences are renamed by their existing signature maps, and the
existing emission of sentences commutes with renaming.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.ITree (Model)
open Silmaril.Logic.ITree.TraceInstitution (Sat allRepliesModel)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation mapOperand mapCaseSignature)
open Silmaril.Isotope.Institution.Acyclic.Captured (GrammarEquation RankedEquation grammarCase readGrammar
  numberGrammar grammarCase_map readGrammar_map grammarCase_roundTrip)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- Request translation commutes with sequencing below a tree without
divergence. -/
theorem tree_bind {S T : Silmaril.Elgot.ITree.Signature.{0}} {X Y : Type 1} (f : S ⟶ T)
    {t : Tree S.Event X} (total : Total t) (k : X → Tree S.Event Y) :
    f.tree id (t >>= k) = (f.tree id t >>= fun x => f.tree id (k x)) :=
  tree_bind_proof f total k

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] (r : Φ → Ψ)

/-- The free tree of a renamed derivation is the request translation of
the free tree of the original derivation, in the same environment. -/
theorem tree_denote {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty (Pulled r) n}
    {A : Ty Empty} (d : Derivation (Pulled r) Γ₀ γ t A) (ρ : BoundEnv Val γ) :
    (renameEvents r).tree id (d.denote Val (model (Pulled r)) (fun x => x.elim) ρ) =
      (renameDerivation r d).denote Val (model Ψ) (fun x => x.elim) ρ :=
  tree_denote_proof r d ρ

/-- The request map of an injective renaming is injective. -/
theorem renameRequest_injective (injective : Function.Injective r) : Function.Injective (renameRequest r) :=
  renameRequest_injective_proof r injective

/-- Every reply map of a renaming is a bijection. -/
theorem renameReply_bijective (q : Request (Events (Pulled r))) :
    Function.Bijective ((renameEvents r).reply q) :=
  renameReply_bijective_proof r q

/-- An injective renaming is a morphism of handled-trace signatures. -/
def renameTrace (injective : Function.Injective r) : events (Pulled r) ⟶ events Ψ :=
  ⟨renameEvents r, renameRequest_injective r injective, renameReply_bijective r⟩

variable {r}

/-- Translating a refinement sentence along the renaming gives the
refinement sentence of the renamed operands. -/
theorem translate_refinement (injective : Function.Injective r) {n : Nat} {γ : Context n} {B : Ty Empty}
    (a b : Operand (Pulled r) γ B) (ρ : BoundEnv Val γ) :
    (refinement a b ρ).translate (renameTrace r injective) =
      refinement (renameOperand r a) (renameOperand r b) ρ :=
  (Logic.ITree.TraceInstitution.translate_hasTrace (renameTrace r injective) _ _).trans
    (by rw [show (renameTrace r injective).hom = renameEvents r from rfl, tree_denote, tree_denote]; rfl)

/-- The satisfaction condition for one renamed refinement sentence. -/
theorem sat_rename (injective : Function.Injective r) (N : HandledModel Ψ) {n : Nat} {γ : Context n}
    {B : Ty Empty} (a b : Operand (Pulled r) γ B) (ρ : BoundEnv Val γ) :
    Sat N (refinement (renameOperand r a) (renameOperand r b) ρ) ↔
      Sat (N.reduct (renameEvents r)) (refinement a b ρ) :=
  (Iff.of_eq (congrArg (Sat N) (translate_refinement injective a b ρ).symm)).trans
    (Logic.ITree.TraceInstitution.satisfaction (renameTrace r injective) N (refinement a b ρ))

/-- The satisfaction condition for renamed typed LetCase sentences. -/
theorem satLe_rename (injective : Function.Injective r) (N : HandledModel Ψ)
    (e : CaseEquation (sig (Pulled r))) :
    SatLe N (renameCase r e) ↔ SatLe (N.reduct (renameEvents r)) e :=
  forall_congr' fun ρ => sat_rename injective N e.2.1 e.2.2 ρ

/-- The renaming as a corridor of the LetCase rooms. Sentences are renamed
and models are reduced along the request map. -/
noncomputable def renameCorridor (injective : Function.Injective r) : caseRoom (Pulled r) ⟶ caseRoom Ψ :=
  ⟨renameCase r, Discrete.functor fun N => Discrete.mk (N.reduct (renameEvents r)),
    fun N e => satLe_rename injective N.as e⟩

variable (r) in
/-- The reduct of the model that admits every reply admits every reply. -/
theorem reduct_allReplies :
    (allRepliesModel (events Ψ)).reduct (renameEvents r) = allRepliesModel (events (Pulled r)) :=
  reduct_allReplies_proof r

/-! ## Comparison with the existing sentence maps -/

/-- At a relabelling, the existing type-changing sentence map keeps the
typing index and applies the fold of the existing LetCase institution. -/
theorem mapCaseSignature_primitive {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (e : CaseEquation P) :
    mapCaseSignature f.toSignatureMap e = ⟨e.1, mapOperand f e.2.1, mapOperand f e.2.2⟩ :=
  mapCaseSignature_primitive_proof f e

variable (r) in
/-- The fold of the existing LetCase institution is the structural renaming. -/
theorem mapOperand_pulled {n : Nat} {γ : Context n} {A : Ty Empty} (a : Operand (Pulled r) γ A) :
    mapOperand (pulledHom r) a = renameOperand r a :=
  mapOperand_pulled_proof r a.2

variable (r) in
/-- The renamed sentence is the sentence map of the existing LetCase
institution at the relabelling. -/
theorem renameCase_eq_inst (e : CaseEquation (sig (Pulled r))) :
    ((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map (pulledHom r)).sen e = renameCase r e :=
  congrArg₂ (fun (x : Operand Ψ e.1.bound e.1.result) (y : Operand Ψ e.1.bound e.1.result) =>
    (⟨e.1, x, y⟩ : CaseEquation (sig Ψ))) (mapOperand_pulled r e.2.1) (mapOperand_pulled r e.2.2)

variable (r) in
/-- The renamed sentence is the existing type-changing sentence map at the
relabelling. The translated index is the original index. -/
theorem mapCaseSignature_pulled (e : CaseEquation (sig (Pulled r))) :
    mapCaseSignature (pulledHom r).toSignatureMap e = renameCase r e :=
  (mapCaseSignature_primitive (pulledHom r) e).trans (renameCase_eq_inst r e)

/-! ## Grammar and ranked sentences -/

variable (r) in
/-- Rendering a renamed grammar sentence renames the rendered sentence. -/
theorem grammarCase_renameGrammar (e : GrammarEquation (sig (Pulled r))) :
    grammarCase (renameGrammar r e) = renameCase r (grammarCase e) :=
  (grammarCase_map (pulledHom r).toSignatureMap e).trans (mapCaseSignature_pulled r (grammarCase e))

variable (r) in
/-- Emitting a renamed ranked sentence renames the emitted grammar sentence. -/
theorem readGrammar_renameRanked (e : RankedEquation (sig (Pulled r))) :
    readGrammar (renameRanked r e) = renameGrammar r (readGrammar e) :=
  readGrammar_map (pulledHom r).toSignatureMap e

variable (r) in
/-- Numbering and renaming in either order emit the same LetCase sentence. -/
theorem grammarCase_number_rename (e : GrammarEquation (sig (Pulled r))) :
    grammarCase (readGrammar (numberGrammar (renameGrammar r e))) =
      grammarCase (readGrammar (renameRanked r (numberGrammar e))) := by
  rw [grammarCase_roundTrip, readGrammar_renameRanked, grammarCase_renameGrammar, grammarCase_renameGrammar,
    grammarCase_roundTrip]

/-- The satisfaction condition for renamed grammar sentences. -/
theorem sat_renameGrammar (injective : Function.Injective r) (N : HandledModel Ψ)
    (e : GrammarEquation (sig (Pulled r))) :
    (grammarRoom Ψ).Sat ⟨N⟩ (renameGrammar r e) ↔
      (grammarRoom (Pulled r)).Sat ⟨N.reduct (renameEvents r)⟩ e :=
  (Iff.of_eq (congrArg (SatLe N) (grammarCase_renameGrammar r e))).trans
    (satLe_rename injective N (grammarCase e))

/-- The satisfaction condition for renamed ranked sentences. -/
theorem sat_renameRanked (injective : Function.Injective r) (N : HandledModel Ψ)
    (e : RankedEquation (sig (Pulled r))) :
    (rankedRoom Ψ).Sat ⟨N⟩ (renameRanked r e) ↔
      (rankedRoom (Pulled r)).Sat ⟨N.reduct (renameEvents r)⟩ e :=
  (Iff.of_eq (congrArg (fun g => SatLe N (grammarCase g)) (readGrammar_renameRanked r e))).trans
    (sat_renameGrammar injective N (readGrammar e))

/-- Numbering a renamed grammar sentence and renaming its numbering hold
in the same models. -/
theorem sat_number_rename (N : (rankedRoom Ψ).Mod) (e : GrammarEquation (sig (Pulled r))) :
    (rankedRoom Ψ).Sat N (numberGrammar (renameGrammar r e)) ↔
      (rankedRoom Ψ).Sat N (renameRanked r (numberGrammar e)) :=
  Iff.of_eq (congrArg (SatLe N.as) (grammarCase_number_rename r e))

/-- Renaming as a corridor of the grammar rooms. -/
noncomputable def renameGrammarCorridor (injective : Function.Injective r) :
    grammarRoom (Pulled r) ⟶ grammarRoom Ψ :=
  ⟨renameGrammar r, Discrete.functor fun N => Discrete.mk (N.reduct (renameEvents r)),
    fun N e => sat_renameGrammar injective N.as e⟩

/-- Renaming as a corridor of the ranked rooms. -/
noncomputable def renameRankedCorridor (injective : Function.Injective r) :
    rankedRoom (Pulled r) ⟶ rankedRoom Ψ :=
  ⟨renameRanked r, Discrete.functor fun N => Discrete.mk (N.reduct (renameEvents r)),
    fun N e => sat_renameRanked injective N.as e⟩

/-- Emission of ranked sentences commutes with renaming, on sentences and
on models. -/
theorem read_rename_square (injective : Function.Injective r) :
    readCorridor (Pulled r) ≫ renameGrammarCorridor injective =
      renameRankedCorridor injective ≫ readCorridor Ψ :=
  Room.hom_ext (funext fun e => (readGrammar_renameRanked r e).symm) rfl

/-- Rendering grammar sentences to LetCase commutes with renaming. -/
theorem grammarCase_rename_square (injective : Function.Injective r) :
    grammarCaseCorridor (Pulled r) ≫ renameCorridor injective =
      renameGrammarCorridor injective ≫ grammarCaseCorridor Ψ :=
  Room.hom_ext (funext fun e => (grammarCase_renameGrammar r e).symm) rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
