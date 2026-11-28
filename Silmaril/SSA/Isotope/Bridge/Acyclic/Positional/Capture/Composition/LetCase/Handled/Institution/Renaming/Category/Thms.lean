module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Category.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Category

/-! # The handled-trace institutions over injective renamings

Signatures are finite structural signatures and signature morphisms are
injective relabellings that keep each argument and reply type. Sentences
are the existing LetCase, grammar and ranked equations, translated by the
existing sentence maps. Models are the existing handled-trace models over
the free requests, reduced along the request map of the relabelling.

Every such relabelling is a pulled-back renaming, which is how the
satisfaction condition is obtained. Emission of ranked sentences and
rendering of grammar sentences are natural in the renaming. Readback is
natural up to satisfaction.

Signature morphisms that translate types are not morphisms here.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.Institution (Room Inst)
open Silmaril.Logic.ITree (Model)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation mapCaseSignature)
open Silmaril.Isotope.Institution.Acyclic.Captured (GrammarEquation RankedEquation grammarCase readGrammar
  mapGrammar mapRanked mapGrammar_id mapGrammar_comp mapRanked_id mapRanked_comp grammarCase_map readGrammar_map)
open LetCase.Structural.Finite (Shape)
open LetCase.Structural.Reply (Γ₀)
open Free (Events)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- A shape is determined by its type. -/
theorem shape_ty_injective : Function.Injective Shape.ty :=
  shape_ty_injective_proof

/-- Every relabelling into a structural signature is a pulled-back
renaming. A property of relabellings holds when it holds for those. -/
theorem hom_cases {Ψ : Type} [LetCase.Structural.Finite.Signature Ψ]
    (motive : ∀ {Φ : Type} [LetCase.Structural.Finite.Signature Φ], (sig Φ ⟶ sig Ψ) → Prop)
    (pulled : ∀ {Φ : Type} (r : Φ → Ψ), motive (pulledHom r))
    {Φ : Type} [LetCase.Structural.Finite.Signature Φ] (f : sig Φ ⟶ sig Ψ) : motive f :=
  hom_cases_proof motive pulled f

variable {Φ Ψ Ω : Type} [LetCase.Structural.Finite.Signature Φ] [LetCase.Structural.Finite.Signature Ψ]
  [LetCase.Structural.Finite.Signature Ω]

/-! ## The request map -/

theorem eventsHom_pulled {Φ : Type} (r : Φ → Ψ) : eventsHom (pulledHom r) = renameEvents r :=
  eventsHom_pulled_proof r

@[simp] theorem eventsHom_id : eventsHom (𝟙 (sig Φ)) = 𝟙 (events Φ).toSignature :=
  eventsHom_id_proof

theorem eventsHom_comp (f : sig Φ ⟶ sig Ψ) (g : sig Ψ ⟶ sig Ω) :
    eventsHom (f ≫ g) = eventsHom f ≫ eventsHom g :=
  eventsHom_comp_proof g f

theorem eventsRequest_injective (f : sig Φ ⟶ sig Ψ) (injective : Function.Injective f.instr) :
    Function.Injective (eventsRequest f) :=
  eventsRequest_injective_proof f injective

theorem eventsReply_bijective (f : sig Φ ⟶ sig Ψ) (q : Request (Events Φ)) :
    Function.Bijective ((eventsHom f).reply q) :=
  eventsReply_bijective_proof f q

/-- A morphism of handled-trace signatures is determined by its request map. -/
theorem traceHom_ext {S T : TraceSignature.{0}} {f g : S ⟶ T} (same : f.hom = g.hom) : f = g :=
  traceHom_ext_proof same

/-- Renamings to the existing handled-trace signatures, as a functor. -/
def eventsFunctor : StructuralSig ⥤ TraceSignature.{0} where
  obj X := events X.Instr
  map f := ⟨eventsHom f.hom, eventsRequest_injective f.hom f.injective, eventsReply_bijective f.hom⟩
  map_id _ := traceHom_ext eventsHom_id
  map_comp f g := traceHom_ext (eventsHom_comp f.hom g.hom)

/-! ## The satisfaction condition -/

/-- A LetCase sentence translated by the existing LetCase institution holds
in a model exactly when the original holds in the reduct. -/
theorem satLe_hom (f : sig Φ ⟶ sig Ψ) (injective : Function.Injective f.instr) (N : HandledModel Ψ)
    (e : CaseEquation (sig Φ)) :
    SatLe N (((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map f).sen e) ↔
      SatLe (N.reduct (eventsHom f)) e :=
  satLe_hom_proof f injective N e

/-- The same for the existing type-changing sentence map at the relabelling. -/
theorem satLe_mapCaseSignature (f : sig Φ ⟶ sig Ψ) (injective : Function.Injective f.instr)
    (N : HandledModel Ψ) (e : CaseEquation (sig Φ)) :
    SatLe N (mapCaseSignature f.toSignatureMap e) ↔ SatLe (N.reduct (eventsHom f)) e :=
  (Iff.of_eq (congrArg (SatLe N) (mapCaseSignature_primitive f e))).trans (satLe_hom f injective N e)

theorem sat_mapGrammar (f : sig Φ ⟶ sig Ψ) (injective : Function.Injective f.instr) (N : HandledModel Ψ)
    (e : GrammarEquation (sig Φ)) :
    (grammarRoom Ψ).Sat ⟨N⟩ (mapGrammar f.toSignatureMap e) ↔
      (grammarRoom Φ).Sat ⟨N.reduct (eventsHom f)⟩ e :=
  (Iff.of_eq (congrArg (SatLe N) (grammarCase_map f.toSignatureMap e))).trans
    (satLe_mapCaseSignature f injective N (grammarCase e))

theorem sat_mapRanked (f : sig Φ ⟶ sig Ψ) (injective : Function.Injective f.instr) (N : HandledModel Ψ)
    (e : RankedEquation (sig Φ)) :
    (rankedRoom Ψ).Sat ⟨N⟩ (mapRanked f.toSignatureMap e) ↔
      (rankedRoom Φ).Sat ⟨N.reduct (eventsHom f)⟩ e :=
  (Iff.of_eq (congrArg (fun g => SatLe N (grammarCase g)) (readGrammar_map f.toSignatureMap e))).trans
    (sat_mapGrammar f injective N (readGrammar e))

/-! ## Institutions over renamings -/

/-- The reduct of the model that admits every reply admits every reply. -/
theorem reduct_allReplies_hom (f : sig Φ ⟶ sig Ψ) :
    (Logic.ITree.TraceInstitution.allRepliesModel (events Ψ)).reduct (eventsHom f) =
      Logic.ITree.TraceInstitution.allRepliesModel (events Φ) :=
  reduct_allReplies_hom_proof f

theorem reductFunctor_id : reductFunctor (𝟙 (sig Φ)) = 𝟭 _ :=
  reductFunctor_id_proof

theorem reductFunctor_comp (f : sig Φ ⟶ sig Ψ) (g : sig Ψ ⟶ sig Ω) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  reductFunctor_comp_proof f g

/-- Directed LetCase sentences over handled-trace models, as a functor
from renamings to rooms. -/
noncomputable def caseInst : StructuralSig ⥤ Room.{0, 1, 1} where
  obj X := caseRoom X.Instr
  map f := ⟨((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map f.hom).sen, reductFunctor f.hom,
    fun N e => satLe_hom f.hom f.injective N.as e⟩
  map_id X := Room.hom_ext
    (congrArg (fun c => c.sen) ((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map_id (sig X.Instr)))
    reductFunctor_id
  map_comp f g := Room.hom_ext
    (congrArg (fun c => c.sen)
      ((Silmaril.Isotope.Institution.LetCase.inst (ε := Bool) Γ₀).map_comp f.hom g.hom))
    (reductFunctor_comp f.hom g.hom)

/-- Directed grammar sentences over handled-trace models. -/
noncomputable def grammarInst : StructuralSig ⥤ Room.{0, 1, 1} where
  obj X := grammarRoom X.Instr
  map f := ⟨mapGrammar f.hom.toSignatureMap, reductFunctor f.hom,
    fun N e => sat_mapGrammar f.hom f.injective N.as e⟩
  map_id _ := Room.hom_ext (funext mapGrammar_id) reductFunctor_id
  map_comp f g := Room.hom_ext
    (funext (mapGrammar_comp f.hom.toSignatureMap g.hom.toSignatureMap)) (reductFunctor_comp f.hom g.hom)

/-- Directed ranked sentences over handled-trace models. -/
noncomputable def rankedInst : StructuralSig ⥤ Room.{0, 1, 1} where
  obj X := rankedRoom X.Instr
  map f := ⟨mapRanked f.hom.toSignatureMap, reductFunctor f.hom,
    fun N e => sat_mapRanked f.hom f.injective N.as e⟩
  map_id _ := Room.hom_ext (funext mapRanked_id) reductFunctor_id
  map_comp f g := Room.hom_ext
    (funext (mapRanked_comp f.hom.toSignatureMap g.hom.toSignatureMap)) (reductFunctor_comp f.hom g.hom)

/-- The three bundled institutions. -/
noncomputable abbrev caseInstitution : Inst.{1, 0, 0, 1, 1} := ⟨StructuralSig, caseInst⟩
noncomputable abbrev grammarInstitution : Inst.{1, 0, 0, 1, 1} := ⟨StructuralSig, grammarInst⟩
noncomputable abbrev rankedInstitution : Inst.{1, 0, 0, 1, 1} := ⟨StructuralSig, rankedInst⟩

/-- Emission of ranked sentences is natural in the renaming. -/
noncomputable def readNatural : rankedInst ⟶ grammarInst where
  app X := readCorridor X.Instr
  naturality _ _ f := Room.hom_ext (funext (readGrammar_map f.hom.toSignatureMap)) rfl

/-- Rendering of grammar sentences to LetCase is natural in the renaming. -/
noncomputable def grammarCaseNatural : grammarInst ⟶ caseInst where
  app X := grammarCaseCorridor X.Instr
  naturality _ _ f := Room.hom_ext
    (funext fun e => (grammarCase_map f.hom.toSignatureMap e).trans (mapCaseSignature_primitive f.hom _)) rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
