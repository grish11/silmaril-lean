module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedBitQuery

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open scoped MonoidalCategory

local notation "E" => Paper.Extension.Eqv Seed

private theorem alias_to_read (label : Bool) :
    E [Bit] (selected label .retainedAlias) (call label (.var 0)) Exits := by
  let body : Region signature.Instr := .let₁ (.var 1) (call label (.var 0))
  have bodyTyped : ValueBranches [Bit, Bit] body Exits :=
    .let₁ (.var (i := 1) rfl) (call_typed label (.var (i := 0) rfl))
  have removeCase : E [Bit] (selected label .retainedAlias)
      (.let₁ (.var 0) (call label (.var 0))) Exits :=
    .paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl) bodyTyped.hasType)))
  exact removeCase.trans
    (.paper (.cfgEta (.native (.letValue (.var (i := 0) rfl)
      (call_typed label (.var (i := 0) rfl)).hasType))))

private theorem unit_payload :
    E [Ty.unit, Bit] (.br 0 (.var 0)) (.br 0 .unit) [Ty.unit] := by
  have eta : E [Ty.unit] (.br 0 .unit) (.br 0 (.var 0)) [Ty.unit] :=
    .extra (.br rfl .unit) (.br rfl (.var (i := 0) rfl)) (.inl (.inl (.inl (.inr .unit))))
  have keep : Ren [Ty.unit] [Ty.unit, Bit] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  simpa only [renameVars_id] using eta.symm.renameVars keep

private theorem reconstruct_to_literal (label right : Bool) :
    E [Ty.unit, Bit] (call label (constructorBit right (.var 0)))
      (arm label right .literal) Exits := by
  have continuation : LSubst.HasType [Ty.unit, Bit] [Ty.unit] Exits
      (fun _ => call label (constructorBit right (.var 0))) := by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact (call_typed label (constructorBit_value right (.var (i := 0) rfl)).hasType).hasType
    | succ i => simp [At] at hi
  cases right <;>
    exact unit_payload.lsubstPost (.br rfl (.var (i := 0) rfl)) (.br rfl .unit) continuation

private theorem literal_to_read (label : Bool) :
    E [Bit] (selected label .literal) (call label (.var 0)) Exits := by
  refine (Paper.Extension.Eqv.case (.var (i := 0) rfl)
    (reconstruct_to_literal label false).symm (reconstruct_to_literal label true).symm).trans ?_
  exact .paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl)
    (call_typed label (.var (i := 0) rfl)).hasType)))

private theorem pack_equiv {r s : Region signature.Instr}
    (hr : ValueBranches [Bit] r Exits) (hs : ValueBranches [Bit] s Exits)
    (h : E [Bit] r s Exits) :
    Paper.Extension.Singleton.ofRegion Seed hr.packExits =
      Paper.Extension.Singleton.ofRegion Seed hs.packExits :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (h.lsubstPost hr hs (fun _ _ hi => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))

theorem packed_replay (label : Bool) : packed label .retainedAlias = packed label .literal :=
  pack_equiv (selected_typed label .retainedAlias) (selected_typed label .literal)
    ((alias_to_read label).trans (literal_to_read label).symm)

theorem request_outcome_iff (label q right payload : Bool) (q' : value Bit) :
    (Except.ok (answer right payload), FreeMonoid.of (⟨label, q, right, payload⟩ : Event))
      ∈ (request label q').outcomes ↔ q' = bit q := by
  rw [request, Tagged.outcomes_ofOutcomes]
  constructor
  · rintro ⟨reply, h⟩
    have event := FreeMonoid.of_injective (congrArg Prod.snd h)
    have tag : queryBit q' = q := congrArg Event.query event
    cases q' with
    | inl u => cases u; cases tag; rfl
    | inr u => cases u; cases tag; rfl
  · rintro rfl
    cases q <;> exact ⟨(right, payload), rfl⟩

private theorem wrong_to_true (label : Bool) :
    E [Bit] (selected label .wrongLiteral)
      (call label (constructorBit true .unit)) Exits :=
  .paper (.cfgEta (.native (.caseValue (.var (i := 0) rfl)
    (call_typed label (Γ := [Bit, Bit]) (constructorBit_value true .unit).hasType).hasType)))

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)
open Silmaril.Isotope.LetIter.Semantics.Categorical (case_return_map)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr :=
  Kleisli.instructions model

local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

private theorem map_selected (label : Bool) (s : Spelling) {arg : Tm signature.Instr}
    (h : Tm.HasType [Bit] arg Bit) (rewrite : E [Bit] (selected label s) (call label arg) Exits) :
    denote.map (packed label s) = denoteSingletonRegion J M (call_typed label h).packExits.hasType := by
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M := Paper.WithCaseBind.joined_seedDenotes J M
    (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)
  have eq : packed label s = Paper.Extension.Singleton.ofRegion Seed (call_typed label h).packExits :=
    pack_equiv (selected_typed label s) (call_typed label h) rewrite
  rw [eq]
  exact Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩) sound _

private noncomputable abbrev exitRoute (i : Nat) (hi : At Exits i Bit) :=
  labelInject M i hi ≫ packLabel M Exits

private noncomputable abbrev sumRoute :=
  coprod.desc (exitRoute 0 rfl) (exitRoute 1 rfl)

private noncomputable abbrev replyRoute : value Answer ⟶ value (packedExitType Exits) :=
  ((M).coprodIso Bit Bit).hom ≫ sumRoute

/-- Denote the unchanged reply continuations and then pack their ordered exits. -/
private theorem call_fold (label : Bool) {arg : Tm signature.Instr} {h : Tm.HasType [Bit] arg Bit}
    {f : (J).obj (ctxObj M [Bit]) ⟶ (J).obj ((M).obj Bit)} (d : Denotes J M h f) :
    denoteSingletonRegion J M (call_typed label h).packExits.hasType =
      (J).map ((λ_ ((M).obj Bit)).inv : (M).obj Bit ⟶ ctxObj M [Bit]) ≫ f ≫
        (Kleisli.instructions model).denote (show signature.Instr from .ask label) ≫
        (J).map replyRoute := by
  change (J).map _ ≫ denoteRegion J M (call_typed label h).hasType.packExits ≫ (J).map _ = _
  rw [denoteRegion_packExits_valueBranches J M (fun _ _ => ⟨rfl, rfl⟩) (call_typed label h)]
  let op : signature.Instr := .ask label
  have dcall : Denotes J M (Tm.HasType.op (f := op) h)
      (f ≫ (Kleisli.instructions model).denote op) := .op d
  have eq := RegionDenotes.eq_denote J M
    (RegionDenotes.case dcall
      (RegionDenotes.br (h := (rfl : At Exits 0 Bit)) (Denotes.var (i := 0) rfl))
      (RegionDenotes.br (h := (rfl : At Exits 1 Bit)) (Denotes.var (i := 0) rfl)))
  erw [← eq]
  simp only [Category.assoc, ← (J).map_comp]
  erw [case_return_map J]
  simp only [packLabelExit, Category.assoc, SingletonDispatcher.labelInject_payload,
    Category.comp_id, ← (J).map_comp, Limits.coprod.desc_comp]
  let intoContext : (J).obj ((M).obj Bit) ⟶ (J).obj (ctxObj M [Bit]) :=
    (J).map ((λ_ ((M).obj Bit)).inv : (M).obj Bit ⟶ ctxObj M [Bit])
  let invoke := (Kleisli.instructions model).denote op
  let toSum := ((M).coprodIso Bit Bit).hom
  change intoContext ≫ ((f ≫ invoke) ≫ (J).map toSum) ≫ (J).map sumRoute =
    intoContext ≫ f ≫ invoke ≫ (J).map replyRoute
  apply congrArg (intoContext ≫ ·)
  calc
    ((f ≫ invoke) ≫ (J).map toSum) ≫ (J).map sumRoute =
        (f ≫ invoke) ≫ ((J).map toSum ≫ (J).map sumRoute) := Category.assoc _ _ _
    _ = (f ≫ invoke) ≫ (J).map replyRoute :=
      congrArg ((f ≫ invoke) ≫ ·) ((J).map_comp toSum sumRoute).symm
    _ = _ := Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem route_apply (v : value Answer) : replyRoute v = atExit v := by
  let sumIso := Types.binaryCoproductIso (value Bit) (value Bit)
  cases v with
  | inl v =>
    have h : TypeCat.ofHom Sum.inl ≫ sumIso.inv ≫ sumRoute =
        packedLabelInject M 0 (rfl : At Exits 0 Bit) := by
      dsimp only [sumIso, sumRoute, exitRoute]
      rw [← Types.binaryCoproductIso_inl_comp_hom, Category.assoc, Iso.hom_inv_id_assoc,
        coprod.inl_desc, labelInject_packLabel]
    refine (ConcreteCategory.congr_hom h v).trans ?_
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
    exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
      (value Bit) (value (packedExitType [Bit]))) v
  | inr v =>
    have h : TypeCat.ofHom Sum.inr ≫ sumIso.inv ≫ sumRoute =
        packedLabelInject M 1 (rfl : At Exits 1 Bit) := by
      dsimp only [sumIso, sumRoute, exitRoute]
      rw [← Types.binaryCoproductIso_inr_comp_hom, Category.assoc, Iso.hom_inv_id_assoc,
        coprod.inr_desc, labelInject_packLabel]
    refine (ConcreteCategory.congr_hom h v).trans ?_
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) v
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit]))) (Sum.inl v : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) v) = _
    rw [inner]
    exact outer

set_option backward.isDefEq.respectTransparency false in
private theorem call_run (label : Bool) {arg : Tm signature.Instr} {h : Tm.HasType [Bit] arg Bit}
    {f : (J).obj (ctxObj M [Bit]) ⟶ (J).obj ((M).obj Bit)} (d : Denotes J M h f) (input q : value Bit)
    (hf : f.of (PUnit.unit, input) = (pure q : Trace (value Bit))) :
    (denoteSingletonRegion J M (call_typed label h).packExits.hasType).of input =
      (request label q >>= fun r => pure (atExit r)) := by
  rw [call_fold label d]
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  simp only [Bind.kleisliRight]
  have step (v : ctxObj M [Bit]) :
      (f ≫ (Kleisli.instructions model).denote (show signature.Instr from .ask label) ≫
        (J).map replyRoute).of v =
      Bind.bind (m := Trace) (f.of v) (fun x =>
        Bind.bind (m := Trace) (request label x) (fun r => pure (atExit r))) := by
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight]
    congr 1
    funext x
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight]
    change Bind.bind (m := Trace) (request label x) _ = _
    congr 1
    funext r
    exact congrArg (pure (f := Trace)) (route_apply r)
  have fold := congrArg (fun k => Bind.bind (m := Trace) (pure (PUnit.unit, input)) k) (funext step)
  refine fold.trans ?_
  simp only [pure_bind, hf]

private theorem selected_run (label : Bool) (s : Spelling) (input : value Bit) :
    (denote.map (packed label s)).of input =
      (request label (s.query input) >>= fun r => pure (atExit r)) := by
  cases s with
  | retainedAlias =>
    rw [map_selected label .retainedAlias (.var (i := 0) rfl) (alias_to_read label)]
    exact call_run label (Denotes.var (i := 0) rfl) input input rfl
  | literal =>
    rw [map_selected label .literal (.var (i := 0) rfl) (literal_to_read label)]
    exact call_run label (Denotes.var (i := 0) rfl) input input rfl
  | wrongLiteral =>
    rw [map_selected label .wrongLiteral (constructorBit_value true .unit).hasType (wrong_to_true label)]
    apply call_run label (.inr .unit) input (bit true)
    erw [← (J).map_comp]
    change (pure ((coprod.inr ≫ (Types.binaryCoproductIso PUnit PUnit).hom) PUnit.unit) :
      Trace (value Bit)) = pure (bit true)
    exact congrArg (pure (f := Trace))
      (ConcreteCategory.congr_hom (Types.binaryCoproductIso_inr_comp_hom PUnit PUnit) PUnit.unit)

/-- Sequencing the reply's pure exit does not change the request event. -/
theorem packed_outcomes (label : Bool) (s : Spelling) (input : value Bit) :
    observations label s input =
      Set.range fun reply : Bool × Bool =>
        (.ok (atExit (answer reply.1 reply.2)),
          FreeMonoid.of ⟨label, queryBit (s.query input), reply.1, reply.2⟩) := by
  unfold observations
  have eq := congrArg (Tagged.outcomes (A := value (packedExitType Exits))) (selected_run label s input)
  refine eq.trans ?_
  apply Set.ext
  intro z
  obtain ⟨result, word⟩ := z
  rw [Tagged.mem_bind]
  simp only [request, Tagged.outcomes_ofOutcomes]
  constructor
  · rintro (⟨fault, _, ⟨pair, bad⟩⟩ | ⟨r, u, v, ⟨reply, hr⟩, hv, hw⟩)
    · cases (congrArg Prod.fst bad : Except.ok (answer pair.1 pair.2) = Except.error fault)
    · have ret : (result, v) = (.ok (atExit r), 1) := hv
      rcases Prod.mk.inj hr with ⟨hr, hu⟩
      rcases Prod.mk.inj ret with ⟨hresult, hv⟩
      refine ⟨reply, Prod.ext ?_ ?_⟩
      · exact (congrArg (fun a => Except.ok (atExit a)) (Except.ok.inj hr)).trans hresult.symm
      · rw [← hw, ← hu, hv, mul_one]
  · rintro ⟨reply, h⟩
    cases h
    exact Or.inr ⟨answer reply.1 reply.2, _, 1, ⟨reply, rfl⟩, rfl, mul_one _⟩

theorem wrong_literal_witness (label : Bool) :
    let observation := (Except.ok (atExit (answer true false)),
      FreeMonoid.of (⟨label, false, true, false⟩ : Event))
    observation ∈ observations label .retainedAlias (bit false) ∧
      observation ∉ observations label .wrongLiteral (bit false) := by
  dsimp only
  rw [packed_outcomes, packed_outcomes]
  refine ⟨⟨(true, false), rfl⟩, ?_⟩
  rintro ⟨reply, h⟩
  have evt := FreeMonoid.of_injective (congrArg Prod.snd h)
  cases (congrArg Event.query evt : true = false)

theorem packed_wrong_ne (label : Bool) : packed label .retainedAlias ≠ packed label .wrongLiteral := by
  intro h
  let observe (f : Paper.Extension.Singleton.ofType Seed Bit ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType Exits)) :=
    ((denote.map f).of (bit false)).outcomes
  have equal : observations label .retainedAlias (bit false) =
      observations label .wrongLiteral (bit false) := congrArg observe h
  exact (wrong_literal_witness label).2 (equal ▸ (wrong_literal_witness label).1)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedBitQuery
