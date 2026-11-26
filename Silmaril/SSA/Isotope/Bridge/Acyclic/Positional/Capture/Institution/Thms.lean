module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Satisfaction

/-! # Satisfaction and signature transport for the captured comparison -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst Room)
open Morphism (SignatureMap)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]

@[simp] theorem mapRanked_id (e : RankedEquation P) :
    mapRanked (P := P) (Q := P) SignatureMap.id e = e := mapRanked_id_proof e

theorem mapRanked_comp (e : RankedEquation P) :
    mapRanked (h.comp g) e = mapRanked h (mapRanked g e) := mapRanked_comp_proof g h e

@[simp] theorem mapGrammar_id (e : GrammarEquation P) :
    mapGrammar (P := P) (Q := P) SignatureMap.id e = e := mapGrammar_id_proof e

theorem mapGrammar_comp (e : GrammarEquation P) :
    mapGrammar (h.comp g) e = mapGrammar h (mapGrammar g e) := mapGrammar_comp_proof g h e

/-- Forward translation commutes on typed witnesses, before any quotient. -/
theorem readGrammar_map (e : RankedEquation P) :
    readGrammar (mapRanked g e) = mapGrammar g (readGrammar e) := read_map_proof g e

theorem readGrammar_finiteExit (e : RankedEquation P) :
    grammarFiniteExit (readGrammar e) = rankedFiniteExit e := read_finite_proof e

theorem numberGrammar_finiteExit (e : GrammarEquation P) :
    rankedFiniteExit (numberGrammar e) = grammarFiniteExit e := number_finite_proof e

theorem rankedFiniteExit_map (e : RankedEquation P) :
    rankedFiniteExit (mapRanked g e) = mapFiniteExit g (rankedFiniteExit e) :=
  map_rankedFiniteExit_proof g e

theorem grammarFiniteExit_map (e : GrammarEquation P) :
    grammarFiniteExit (mapGrammar g e) = mapFiniteExit g (grammarFiniteExit e) :=
  map_grammarFiniteExit_proof g e

/-- The actual LetCase equation and its result typing commute with signature change. -/
theorem grammarCase_map (e : GrammarEquation P) :
    grammarCase (mapGrammar g e) = mapCaseSignature g (grammarCase e) :=
  (congrArg compileFiniteExit (grammarFiniteExit_map g e)).trans (compileFiniteExit_map g _)

/-- Both orders of reverse compilation and signature change have the same
exact finite-exit lowering. This comparison retains all outward positions. -/
theorem numberGrammar_map_finiteExit (e : GrammarEquation P) :
    rankedFiniteExit (numberGrammar (mapGrammar g e)) =
      rankedFiniteExit (mapRanked g (numberGrammar e)) :=
  (numberGrammar_finiteExit _).trans ((grammarFiniteExit_map g e).trans
    ((congrArg (mapFiniteExit g) (numberGrammar_finiteExit e).symm).trans (rankedFiniteExit_map g _).symm))

/-- Reading back after numbering recovers the actual exact LetCase equation. -/
theorem grammarCase_roundTrip (e : GrammarEquation P) :
    grammarCase (readGrammar (numberGrammar e)) = grammarCase e :=
  congrArg compileFiniteExit ((readGrammar_finiteExit _).trans (numberGrammar_finiteExit e))

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {d : Nat} {β : BoundCtx τ d} {L : List τ}

theorem denoteRanked_map (K : CoherentRegionModel J Q) (p : RankedEntry P.Instr β L) :
    HEq (denoteRanked J (K.pullbackOfWitness g (regionWitnessPullback g K)) p)
      (denoteRanked J K (p.mapSignature g)) :=
  denoteRanked_map_proof g K p

/-- Numbering the emitted grammar preserves the native arrow, including all
outward positions, even when the table changes its local sharing. -/
theorem denoteRanked_roundTrip (K : CoherentRegionModel J P) (p : RankedEntry P.Instr β L) :
    denoteRanked J K (ofGrammar p.toGrammar) = denoteRanked J K p :=
  denote_read_number_proof K p

theorem sat_rankedFiniteExit (K : (rankedRoom J P).Mod) (e : RankedEquation P) :
    (finiteExitRoom J P).Sat K (rankedFiniteExit e) ↔ (rankedRoom J P).Sat K e :=
  sat_ranked_finite_proof K e

theorem sat_readGrammar (A : (grammarRoom J P).Mod) (e : RankedEquation P) :
    (grammarRoom J P).Sat A (readGrammar e) ↔
      (rankedRoom J P).Sat ((validatedCompileCorridor J P).mod.obj A) e :=
  sat_read_proof A e

theorem sat_numberGrammar (K : (rankedRoom J P).Mod) (e : GrammarEquation P) :
    (rankedRoom J P).Sat K (numberGrammar e) ↔
      (grammarRoom J P).Sat ((validatedReifyCorridor J P).mod.obj K) e :=
  sat_number_proof K e

theorem sat_mapRanked (K : (rankedRoom J Q).Mod) (e : RankedEquation P) :
    (rankedRoom J Q).Sat K (mapRanked g e) ↔
      (rankedRoom J P).Sat ((ssaSignatureCorridor g).mod.obj K) e :=
  sat_mapRanked_proof g K e

omit [FreydCategory.CentralUnit J] in
theorem sat_mapGrammar (A : (grammarRoom J Q).Mod) (e : GrammarEquation P) :
    (grammarRoom J Q).Sat A (mapGrammar g e) ↔
      (grammarRoom J P).Sat ((validatedCorridor g).mod.obj A) e :=
  sat_mapGrammar_proof g A e

/-- Reverse translation commutes with signature change in each target model's
native ordered-exit satisfaction. -/
theorem sat_numberGrammar_map (K : (rankedRoom J Q).Mod) (e : GrammarEquation P) :
    (rankedRoom J Q).Sat K (numberGrammar (mapGrammar g e)) ↔
      (rankedRoom J Q).Sat K (mapRanked g (numberGrammar e)) :=
  (sat_rankedFiniteExit K _).symm.trans
    ((Iff.of_eq (congrArg ((finiteExitRoom J Q).Sat K) (numberGrammar_map_finiteExit g e))).trans
      (sat_rankedFiniteExit K _))

/-- Exact lowering compares the existing finite-exit equation with native
satisfaction in the same coherent model. -/
noncomputable def rankedFiniteExitCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : rankedRoom J P ⟶ finiteExitRoom J P :=
  ⟨rankedFiniteExit, 𝟭 _, sat_rankedFiniteExit⟩

/-- Forget the witness, retaining actual validated LetCase satisfaction. -/
noncomputable def grammarCaseCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : grammarRoom J P ⟶ validatedRoom J P :=
  ⟨grammarCase, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- The two rooms use the existing discrete model categories. The forward
model map is validated expansion. -/
noncomputable def readCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : rankedRoom J P ⟶ grammarRoom J P :=
  ⟨readGrammar, (validatedCompileCorridor J P).mod, sat_readGrammar⟩

/-- The reverse model map presents the existing coherent interpretation as
a validated algebra. -/
noncomputable def numberCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : grammarRoom J P ⟶ rankedRoom J P :=
  ⟨numberGrammar, (validatedReifyCorridor J P).mod, sat_numberGrammar⟩

noncomputable def rankedSignatureCorridor : rankedRoom J P ⟶ rankedRoom J Q :=
  ⟨mapRanked g, (ssaSignatureCorridor g).mod, sat_mapRanked g⟩

noncomputable def grammarSignatureCorridor : grammarRoom J P ⟶ grammarRoom J Q :=
  ⟨mapGrammar g, (validatedCorridor g).mod, sat_mapGrammar g⟩

noncomputable def rankedInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : TypeSignature ⥤ Room.{0, 0, 1} where
  obj P := rankedRoom J P.prim
  map f := rankedSignatureCorridor f.signatureMap
  map_id P := Room.hom_ext (funext mapRanked_id)
    (congrArg (fun c : ssaRoom J P.prim ⟶ ssaRoom J P.prim => c.mod) ssaSignatureCorridor_id)
  map_comp {P _ S} f g := Room.hom_ext (funext (mapRanked_comp f.signatureMap g.signatureMap))
    (congrArg (fun c : ssaRoom J P.prim ⟶ ssaRoom J S.prim => c.mod)
      (ssaSignatureCorridor_comp f.signatureMap g.signatureMap))

noncomputable def grammarInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : TypeSignature ⥤ Room.{0, 0, 1} where
  obj P := grammarRoom J P.prim
  map f := grammarSignatureCorridor f.signatureMap
  map_id P := Room.hom_ext (funext mapGrammar_id)
    (congrArg (fun c : validatedRoom J P.prim ⟶ validatedRoom J P.prim => c.mod) validatedCorridor_id)
  map_comp {P _ S} f g := Room.hom_ext (funext (mapGrammar_comp f.signatureMap g.signatureMap))
    (congrArg (fun c : validatedRoom J P.prim ⟶ validatedRoom J S.prim => c.mod)
      (validatedCorridor_comp f.signatureMap g.signatureMap))

noncomputable abbrev rankedInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, rankedInst J⟩

noncomputable abbrev grammarInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, grammarInst J⟩

/-- The forward natural transformation uses the exact signature square on
witnesses and the checked expansion square on models. -/
noncomputable def readNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : rankedInst J ⟶ grammarInst J where
  app P := readCorridor J P.prim
  naturality {P Q} f := Room.hom_ext (funext (readGrammar_map f.signatureMap))
    (congrArg (fun c : ssaRoom J P.prim ⟶ validatedRoom J Q.prim => c.mod)
      (validatedCompile_natural f.signatureMap))

/-- Forgetting the witness is natural into the existing validated institution. -/
noncomputable def grammarCaseNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : grammarInst J ⟶ validatedTypeInst J where
  app P := grammarCaseCorridor J P.prim
  naturality {_ _} f := Room.hom_ext
    (funext fun e => (grammarCase_map f.signatureMap e).trans (typeCaseHom_translate f.signatureMap _).symm)
    rfl

/-- The existing finite-exit institution sees the same checked lowering over
the full signature category. -/
noncomputable def rankedFiniteExitNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : rankedInst J ⟶ finiteExitInst J where
  app P := rankedFiniteExitCorridor J P.prim
  naturality {_ _} f := Room.hom_ext (funext (rankedFiniteExit_map f.signatureMap))
    rfl

/-- The witnessed comparison factors the existing finite-exit compilation,
including its model functors. -/
theorem readNatural_grammarCaseNatural (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    readNatural J ≫ grammarCaseNatural J = rankedFiniteExitNatural J ≫ compileFiniteExitNatural J :=
  NatTrans.ext (funext fun _ => Room.hom_ext
    (funext fun e => congrArg compileFiniteExit (readGrammar_finiteExit e)) rfl)

end Silmaril.Isotope.Institution.Acyclic.Captured
