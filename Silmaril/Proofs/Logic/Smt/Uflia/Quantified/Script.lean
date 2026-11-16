module

public import Silmaril.Logic.Smt.Uflia.Quantified.Script.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.Script
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution
open Silmaril.Logic.Smt.Uflia.SExpr

/-- Every original assertion is interpreted in the same supplied model. -/
theorem holds_iff (s : Accepted) (M : Packaged.GlobalModel) :
    s.Holds M ↔ s.toWhole.Holds M := by
  change (∀ expression ∈ s.layout.assertions,
    Quantified.SExpr.Surface.Holds s.checked.environment
      (M.reduct (Packaged.nameMap s.checked.environment)) expression) ↔
    ∀ sentence ∈ s.assertions.map (·.sentence),
      Quantified.Sentence.Holds sentence
        (M.reduct (Packaged.nameMap s.checked.environment))
  rw [← s.assertions_eq]
  constructor
  · intro h sentence member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    exact (Quantified.SExpr.Surface.holds_iff_of_decoded _ a.decoded).mp
      (h a.expression (List.mem_map.mpr ⟨a, ha, rfl⟩))
  · intro h expression member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    exact (Quantified.SExpr.Surface.holds_iff_of_decoded _ a.decoded).mpr
      (h a.sentence (List.mem_map.mpr ⟨a, ha, rfl⟩))

noncomputable def decodeCorridor : room ⟶ wholeRoom where
  sen := Accepted.toWhole
  mod := Disc.functor id
  sat M s := (holds_iff s M).symm

theorem decodeCorridor_modelExpansive : decodeCorridor.ModelExpansive :=
  fun M => ⟨M, rfl⟩

noncomputable def decodeComorphism : Comorphism institution wholeInstitution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => Accepted.toWhole) (fun _ => id)
    (fun _ M s => (holds_iff s M).symm) (fun _ _ => rfl) (fun _ _ => rfl)

/-- All original local operations are recovered when declaration names are
injective at each typed profile. No quantifier-specific expansion assumption. -/
noncomputable def packagingCorridor (E : Environment) : fixedRoom E.signature ⟶ wholeRoom where
  sen problem := ⟨E, problem⟩
  mod := Disc.functor (fun M : Packaged.GlobalModel => M.reduct (Packaged.nameMap E))
  sat _ _ := Iff.rfl

theorem packaging_modelExpansive (E : Environment) (h : Packaged.NamesInjective E) :
    (packagingCorridor E).ModelExpansive :=
  fun M => ⟨Packaged.expand E M, Packaged.expand_reduct E h M⟩

theorem checked_packaging_modelExpansive (checked : DeclarationPrefix) :
    (packagingCorridor checked.environment).ModelExpansive :=
  packaging_modelExpansive checked.environment (Packaged.checked_namesInjective checked)

/-- One fixed-signature model expands to one global model for the entire list. -/
theorem whole_sat_iff (p : Whole) (h : Packaged.NamesInjective p.environment) :
    (∃ M, p.Holds M) ↔ ∃ M, FixedHolds p.assertions M := by
  constructor
  · rintro ⟨M, truth⟩
    exact ⟨M.reduct (Packaged.nameMap p.environment), truth⟩
  · rintro ⟨M, truth⟩
    refine ⟨Packaged.expand p.environment M, ?_⟩
    change FixedHolds p.assertions ((Packaged.expand p.environment M).reduct _)
    rw [Packaged.expand_reduct _ h]
    exact truth

theorem sat_iff_fixed (s : Accepted) : s.Sat ↔
    ∃ M, FixedHolds (s.assertions.map (·.sentence)) M :=
  (show (∃ M, s.Holds M) ↔ ∃ M, s.toWhole.Holds M from
    exists_congr (holds_iff s)).trans
      (whole_sat_iff s.toWhole (Packaged.checked_namesInjective s.checked))

theorem unsat_iff_fixed (s : Accepted) : s.Unsat ↔
    ¬ ∃ M, FixedHolds (s.assertions.map (·.sentence)) M :=
  not_congr (sat_iff_fixed s)

/-- Direct source truth in every local model agrees before any global expansion. -/
theorem fixed_holds_iff (s : Accepted) (M : Model s.checked.environment.signature) :
    (∀ e ∈ s.layout.assertions, Quantified.SExpr.Surface.Holds _ M e) ↔
      FixedHolds (s.assertions.map (·.sentence)) M := by
  rw [← s.assertions_eq]
  simp only [List.forall_mem_map, FixedHolds]
  constructor
  · intro h a ha
    exact (Quantified.SExpr.Surface.holds_iff_of_decoded _ a.decoded).mp (h a ha)
  · intro h a ha
    exact (Quantified.SExpr.Surface.holds_iff_of_decoded _ a.decoded).mpr (h a ha)

theorem rejected_neither {text : String} (rejected : accept? text = none) :
    ¬ TextSat text ∧ ¬ TextUnsat text := by
  constructor <;> rintro ⟨s, accepted, _⟩ <;> rw [rejected] at accepted <;> cases accepted

end Silmaril.Logic.Smt.Uflia.Quantified.Script
