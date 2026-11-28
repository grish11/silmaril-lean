module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room Corridor)
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (FiniteExit)
open LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse

set_option backward.isDefEq.respectTransparency false

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]
  {d : Nat} {β : BoundCtx τ d} {L : List τ}

private theorem ranked_map_id (p : RankedEntry P.Instr β L) :
    HEq (p.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) p := by
  have ht := p.table.mapSignature_id_heq
  have he := operandSignature_id_heq p.entry
  cases p
  simp only [RankedEntry.mapSignature]
  congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.id]

private theorem ranked_map_comp (p : RankedEntry P.Instr β L) :
    HEq (p.mapSignature (h.comp g)) ((p.mapSignature g).mapSignature h) := by
  have ht := p.table.mapSignature_comp_heq g h
  have he := operandSignature_comp_heq g h p.entry
  cases p
  simp only [RankedEntry.mapSignature]
  congr! (config := .unfoldSameFun) 1 <;> simp [SignatureMap.comp, List.map_map]

theorem mapRanked_id_proof (e : RankedEquation P) :
    mapRanked (P := P) (Q := P) SignatureMap.id e = e := by
  obtain ⟨⟨depth, β, L⟩, l, r⟩ := e
  have hl := ranked_map_id l
  have hr := ranked_map_id r
  unfold mapRanked
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.id]

theorem mapRanked_comp_proof (e : RankedEquation P) :
    mapRanked (h.comp g) e = mapRanked h (mapRanked g e) := by
  obtain ⟨⟨depth, β, L⟩, l, r⟩ := e
  have hl := ranked_map_comp g h l
  have hr := ranked_map_comp g h r
  unfold mapRanked
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.comp, List.map_map]

theorem mapGrammar_id_proof (e : GrammarEquation P) :
    mapGrammar (P := P) (Q := P) SignatureMap.id e = e := by
  obtain ⟨⟨depth, β, L⟩, l, r⟩ := e
  have hl := l.mapSignature_id_heq
  have hr := r.mapSignature_id_heq
  unfold mapGrammar
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.id]

theorem mapGrammar_comp_proof (e : GrammarEquation P) :
    mapGrammar (h.comp g) e = mapGrammar h (mapGrammar g e) := by
  obtain ⟨⟨depth, β, L⟩, l, r⟩ := e
  have hl := l.mapSignature_comp_heq g h
  have hr := r.mapSignature_comp_heq g h
  unfold mapGrammar
  congr! (config := .unfoldSameFun) 2 <;> simp [SignatureMap.comp, List.map_map]

private theorem read_map_entry (p : RankedEntry P.Instr β L) :
    (p.mapSignature g).toGrammar = p.toGrammar.mapSignature g :=
  tableProgram_mapSignature g p.table p.checked p.index p.entry _

theorem read_map_proof (e : RankedEquation P) :
    readGrammar (mapRanked g e) = mapGrammar g (readGrammar e) := by
  simp only [mapRanked, readGrammar, mapGrammar, read_map_entry]

theorem read_finite_proof (e : RankedEquation P) :
    grammarFiniteExit (readGrammar e) = rankedFiniteExit e :=
  congrArg (fun sides => (⟨e.1, sides⟩ : FiniteExitEquation P))
    (Prod.ext (tableProgram_render _ _ _ _) (tableProgram_render _ _ _ _))

theorem number_finite_proof (e : GrammarEquation P) :
    rankedFiniteExit (numberGrammar e) = grammarFiniteExit e :=
  congrArg (fun sides => (⟨e.1, sides⟩ : FiniteExitEquation P))
    (Prod.ext e.2.1.toTable_render e.2.2.toTable_render)

private theorem ranked_finite_map_entry (p : RankedEntry P.Instr β L) :
    (p.mapSignature g).toFiniteExit = p.toFiniteExit.mapSignature g :=
  (tableProgram_render _ _ _ _).symm.trans
    ((congrArg Program.toFiniteExit (read_map_entry g p)).trans
      ((p.toGrammar.toFiniteExit_mapSignature g).trans
        (congrArg (FiniteExit.mapSignature g) (tableProgram_render p.table p.checked p.index p.entry))))

theorem map_rankedFiniteExit_proof (e : RankedEquation P) :
    rankedFiniteExit (mapRanked g e) = mapFiniteExit g (rankedFiniteExit e) := by
  simp only [rankedFiniteExit, mapRanked, mapFiniteExit, ranked_finite_map_entry]

theorem map_grammarFiniteExit_proof (e : GrammarEquation P) :
    grammarFiniteExit (mapGrammar g e) = mapFiniteExit g (grammarFiniteExit e) := by
  simp only [grammarFiniteExit, mapGrammar, mapFiniteExit, Program.toFiniteExit_mapSignature]

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

private theorem denote_ranked_finite (K : CoherentRegionModel J P) (p : RankedEntry P.Instr β L) :
    K.denoteFiniteExit J p.toFiniteExit = denoteRanked J K p := by
  let _ := K.instructions
  let _ := K.coherent
  exact p.table.toFiniteExit_denote J K.types p.checked p.index p.entry

theorem denoteRanked_map_proof (K : CoherentRegionModel J Q) (p : RankedEntry P.Instr β L) :
    HEq (denoteRanked J (K.pullbackOfWitness g (regionWitnessPullback g K)) p)
      (denoteRanked J K (p.mapSignature g)) := by
  let K' := K.pullbackOfWitness g (regionWitnessPullback g K)
  exact (heq_of_eq (denote_ranked_finite K' p).symm).trans
    ((denoteFiniteExit_pullback g K p.toFiniteExit).trans (heq_of_eq
      ((congrArg (K.denoteFiniteExit J) (ranked_finite_map_entry g p).symm).trans
        (denote_ranked_finite K (p.mapSignature g)))))

theorem sat_ranked_finite_proof (K : (rankedRoom J P).Mod) (e : RankedEquation P) :
    (finiteExitRoom J P).Sat K (rankedFiniteExit e) ↔ (rankedRoom J P).Sat K e := by
  change K.fromShrinkHoms.as.denoteFiniteExit J e.2.1.toFiniteExit =
    K.fromShrinkHoms.as.denoteFiniteExit J e.2.2.toFiniteExit ↔ _
  rw [denote_ranked_finite, denote_ranked_finite]
  rfl

private theorem denote_number (K : CoherentRegionModel J P) (p : Program P.Instr β L) :
    denoteRanked J K (ofGrammar p) = K.denoteFiniteExit J p.toFiniteExit :=
  (denote_ranked_finite K (ofGrammar p)).symm.trans (congrArg (K.denoteFiniteExit J) p.toTable_render)

theorem sat_mapRanked_proof (K : (rankedRoom J Q).Mod) (e : RankedEquation P) :
    (rankedRoom J Q).Sat K (mapRanked g e) ↔
      (rankedRoom J P).Sat ((ssaSignatureCorridor g).mod.obj K) e := by
  have h := sat_ranked_finite_proof K (mapRanked g e)
  rw [map_rankedFiniteExit_proof] at h
  exact h.symm.trans (((finiteExitCorridor g).sat K (rankedFiniteExit e)).trans
    (sat_ranked_finite_proof _ e))

omit [FreydCategory.CentralUnit J] in
theorem sat_mapGrammar_proof (A : (grammarRoom J Q).Mod) (e : GrammarEquation P) :
    (grammarRoom J Q).Sat A (mapGrammar g e) ↔
      (grammarRoom J P).Sat ((validatedCorridor g).mod.obj A) e := by
  change (validatedRoom J Q).Sat A (compileFiniteExit (grammarFiniteExit (mapGrammar g e))) ↔ _
  rw [map_grammarFiniteExit_proof, compileFiniteExit_map, ← typeCaseHom_translate]
  exact (validatedCorridor g).sat A (grammarCase e)

theorem sat_read_proof (A : (grammarRoom J P).Mod) (e : RankedEquation P) :
    (grammarRoom J P).Sat A (readGrammar e) ↔
      (rankedRoom J P).Sat ((validatedCompileCorridor J P).mod.obj A) e := by
  change (validatedRoom J P).Sat A (compileFiniteExit (grammarFiniteExit (readGrammar e))) ↔ _
  rw [read_finite_proof]
  exact (sat_compileFiniteExit A _).trans (sat_ranked_finite_proof _ e)

theorem sat_number_proof (K : (rankedRoom J P).Mod) (e : GrammarEquation P) :
    (rankedRoom J P).Sat K (numberGrammar e) ↔
      (grammarRoom J P).Sat ((validatedReifyCorridor J P).mod.obj K) e := by
  have hc := sat_compileFiniteExit ((validatedReifyCorridor J P).mod.obj K) (grammarFiniteExit e)
  have h := Functor.congr_obj (validatedModelIso (J := J) P).counit_eq K
  change (validatedCompileCorridor J P).mod.obj ((validatedReifyCorridor J P).mod.obj K) = K at h
  rw [h] at hc
  exact (sat_ranked_finite_proof K _).symm.trans
    ((Iff.of_eq (congrArg ((finiteExitRoom J P).Sat K) (number_finite_proof e))).trans hc.symm)

theorem denote_read_number_proof (K : CoherentRegionModel J P) (p : RankedEntry P.Instr β L) :
    denoteRanked J K (ofGrammar p.toGrammar) = denoteRanked J K p := by
  let _ := K.instructions
  let _ := K.coherent
  exact (denote_number K p.toGrammar).trans
    ((congrArg (K.denoteFiniteExit J) (tableProgram_render p.table p.checked p.index p.entry)).trans
      (p.table.toFiniteExit_denote J K.types p.checked p.index p.entry))

end Silmaril.Isotope.Institution.Acyclic.Captured
