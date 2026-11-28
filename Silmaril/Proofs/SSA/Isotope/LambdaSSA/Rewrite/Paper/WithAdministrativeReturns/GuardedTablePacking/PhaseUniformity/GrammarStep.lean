module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TagsGrammar

/-! # The step equation of every row, at every size -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow emptyDispatchRep)
open Paper.TypeCategory (sumInl sumInr blockRoute blockStep iterate_blockStep iterate_fixpoint)
open Paper.TypeCategory (whiskerLeft_iterate iterate_naturality)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback (carryExit)

/-! ## A state tag under renaming and substitution -/

theorem injTm_rename : ∀ (K : Nat) (j : Fin (K + 1)) (a : Tm signature.Instr) (ρ : Nat → Nat),
    (injTm K j a).rename ρ = injTm K j (a.rename ρ)
  | 0, _, _, _ => rfl
  | K + 1, j, a, ρ => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact congrArg Tm.inr (injTm_rename K j a ρ)

theorem injTm_subst : ∀ (K : Nat) (j : Fin (K + 1)) (a : Tm signature.Instr) (θ : Nat → Tm signature.Instr),
    (injTm K j a).subst θ = injTm K j (a.subst θ)
  | 0, _, _, _ => rfl
  | K + 1, j, a, θ => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact congrArg Tm.inr (injTm_subst K j a θ)

/-! ## Factoring out a request -/

/-- A substituted payload commutes with one more weakening. -/
theorem commute_arm (C : Region signature.Instr) (a : Tm signature.Instr) (ha : a.rename (lift Nat.succ) = a) :
    ((C.renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars (Tm.singleSubst a) =
      ((C.renameVars (lift Nat.succ)).substVars (Tm.singleSubst a)).renameVars (lift Nat.succ) := by
  rw [Region.substVars_renameVars, Region.substVars_renameVars, Region.renameVars_substVars,
    Region.substVars_renameVars]
  congr 1
  funext i
  cases i with
  | zero => exact ha.symm
  | succ n => rfl

/-- One request on the newest variable, with the two reply payloads at
two exits. -/
def askExits (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 0 (.var 0)) (.br 1 (.var 0))

theorem askExits_typed (l : Bool) : ValueBranches [Bit] (askExits l) [Bit, Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 0) (A := Bit) rfl (.var (i := 0) rfl))
    (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))

def pairExits : Nat → Region signature.Instr
  | 0 => .br 0 (.inl (.var 0))
  | _ + 1 => .br 0 (.inr (.var 0))

/-- The request with its reply as one sum. -/
def askPair (l : Bool) : Region signature.Instr := (askExits l).lsubst pairExits

theorem askPair_typed (l : Bool) : ValueBranches [Bit] (askPair l) [Silmaril.coprod Bit Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var (i := 0) rfl)))
    (.br rfl (.inr (.var (i := 0) rfl)))

/-- The continuations of a request that do not use its operand. -/
def askConts (L R : Region signature.Instr) : Nat → Region signature.Instr
  | 0 => L.renameVars (lift Nat.succ)
  | _ + 1 => R.renameVars (lift Nat.succ)

/-- A request followed by a continuation for each reply. -/
def askCase (l : Bool) (L R : Region signature.Instr) : Region signature.Instr :=
  (askExits l).lsubst (askConts L R)

section Factor

variable {E : Ty Empty} {L R : Region signature.Instr}

theorem askConts_typed (hL : ValueBranches [Bit] L [E]) (hR : ValueBranches [Bit] R [E]) :
    LSubst.ValueFamily [Bit] [Bit, Bit] [E] (askConts L R)
  | 0, _, h => by
    cases h
    exact hL.renameVars headerRen
  | 1, _, h => by
    cases h
    exact hR.renameVars headerRen

theorem askCase_typed (l : Bool) (hL : ValueBranches [Bit] L [E]) (hR : ValueBranches [Bit] R [E]) :
    ValueBranches [Bit] (askCase l L R) [E] :=
  (askExits_typed l).lsubst (askConts_typed hL hR)

theorem inlB_typed : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit Bit] :=
  .br rfl (.inl (.var rfl))

theorem inrB_typed : ValueBranches [Bit] (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit Bit] :=
  .br rfl (.inr (.var rfl))

/-- A request followed by a case on its reply is the request with the two
arms as continuations. Default Paper: congruence under the request, and
the native case on a constructor in each arm. -/
theorem ask_factor (l : Bool) (hL : ValueBranches [Bit] L [E]) (hR : ValueBranches [Bit] R [E]) :
    ofRegion (askCase_typed l hL hR) = ofRegion (askPair_typed l) ≫ ofRegion (caseValueBranches hL hR) := by
  have hC := caseValueBranches hL hR
  refine ((Paper.TypeCategory.ofRegion_eq_iff (seqValueBranches (askPair_typed l) hC)
    (askCase_typed l hL hR)).mpr ?_).symm.trans
    (ofRegion_comp (askPair_typed l) hC (seqValueBranches (askPair_typed l) hC)).symm
  have e := lsubst_comp (askExits l) pairExits
    (fun _ => (Region.case (.var 0) (L.renameVars (lift Nat.succ))
      (R.renameVars (lift Nat.succ)) : Region signature.Instr).renameVars (lift Nat.succ))
  refine e ▸ Paper.Eqv.lsubstCongr (askExits_typed l) (fun i A h => ?_)
  match i, h with
  | 0, h =>
    cases h
    have k := commute_arm (Region.case (.var 0) (L.renameVars (lift Nat.succ)) (R.renameVars (lift Nat.succ)))
      (.inl (.var 0)) rfl
    have step : Paper.Eqv [Bit, Bit]
        ((((Region.case (.var 0) (L.renameVars (lift Nat.succ)) (R.renameVars (lift Nat.succ)) :
          Region signature.Instr).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
          (Tm.singleSubst (.inl (.var 0)))) (L.renameVars (lift Nat.succ)) [E] := by
      rw [k]
      exact Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
        ((case_inl_arrow (X := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl) hL hR).trans
          (seq_idBit hL))) (headerRen (S := Bit))
    exact step
  | 1, h =>
    cases h
    have k := commute_arm (Region.case (.var 0) (L.renameVars (lift Nat.succ)) (R.renameVars (lift Nat.succ)))
      (.inr (.var 0)) rfl
    have step : Paper.Eqv [Bit, Bit]
        ((((Region.case (.var 0) (L.renameVars (lift Nat.succ)) (R.renameVars (lift Nat.succ)) :
          Region signature.Instr).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
          (Tm.singleSubst (.inr (.var 0)))) (R.renameVars (lift Nat.succ)) [E] := by
      rw [k]
      exact Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
        ((case_inr_arrow (X := Bit) (A := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
          hL hR).trans (seq_idBit hR))) (headerRen (S := Bit))
    exact step

end Factor

/-! ## The leaves of a row -/

section Step

variable {K K' : Nat}

theorem nleaf_norm : (b : NLeaf K) →
    ((b.free.renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = b.free
  | .exit => rfl
  | .goto j =>
    congrArg (fun u : Tm signature.Instr => Region.br 0 (.inr u))
      ((congrArg (fun u : Tm signature.Instr => (u.rename (lift Nat.succ)).subst (Tm.singleSubst (.var 0)))
        (packedExitArg_rename0 j.val (lift Nat.succ) rfl)).trans
        ((congrArg (fun u : Tm signature.Instr => u.subst (Tm.singleSubst (.var 0)))
          (packedExitArg_rename0 j.val (lift Nat.succ) rfl)).trans
          (packedExitArg_subst0 j.val (Tm.singleSubst (.var 0)) rfl)))

/-- The capture-free row of a block is its request followed by its two leaves. -/
theorem free_as_ask (d : NTable K) (i : Fin (K + 1)) :
    d.free i = askCase (d.label i) (d.branch i false).free (d.branch i true).free :=
  (congrArg₂ (fun x y : Region signature.Instr =>
      Region.case (.op (.ask (d.label i) : signature.Instr) (.var 0)) x y)
    (nleaf_norm (d.branch i false)) (nleaf_norm (d.branch i true))).symm

theorem goVarK_typed (j : Fin (K + 1)) :
    ValueBranches [Bit] (.br 0 (.inr (injTm K j (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inr (injTm_typed (.inl (.var rfl)) K j))

/-- A continuation at row `j` with a Bit is the case of the two actions
on the two payloads: a Bit as the case of its constructors, and the state
tag under substitution. -/
theorem goVarK_eta (j : Fin (K + 1)) :
    ofRegion (goVarK_typed j) =
      ofRegion (caseValueBranches (act_typed K (.go j false)) (act_typed K (.go j true))) := by
  have e₀ : ofRegion (seqValueBranches inlU_typed (goVarK_typed j)) = ofRegion (act_typed K (.go j false)) :=
    ofRegion_congr (congrArg (fun u : Tm signature.Instr => Region.br 0 (.inr u))
      ((congrArg (fun u : Tm signature.Instr => u.subst (Tm.singleSubst (.inl (.var 0))))
        (injTm_rename K j (.inl (.var 0)) (lift Nat.succ))).trans
        (injTm_subst K j (.inl (.var 0)) (Tm.singleSubst (.inl (.var 0)))))) _ _
  have e₁ : ofRegion (seqValueBranches inrU_typed (goVarK_typed j)) = ofRegion (act_typed K (.go j true)) :=
    ofRegion_congr (congrArg (fun u : Tm signature.Instr => Region.br 0 (.inr u))
      ((congrArg (fun u : Tm signature.Instr => u.subst (Tm.singleSubst (.inr (.var 0))))
        (injTm_rename K j (.inl (.var 0)) (lift Nat.succ))).trans
        (injTm_subst K j (.inl (.var 0)) (Tm.singleSubst (.inr (.var 0)))))) _ _
  exact (bit_eta (goVarK_typed j)).trans
    ((coprod_desc_ofRegion (seqValueBranches inlU_typed (goVarK_typed j))
      (seqValueBranches inrU_typed (goVarK_typed j))).symm.trans
      ((congrArg₂ (fun u v => (sumIso (Φ := signature.Instr) U U).hom ≫ coprod.desc u v) e₀ e₁).trans
        (coprod_desc_ofRegion (act_typed K (.go j false)) (act_typed K (.go j true)))))

/-- A leaf with its tag sent to a state is the case of its two actions:
the sum injection for an exit, and the tag map for a jump. -/
theorem nleaf_post : (b : NLeaf K) →
    ofRegion (nleaf_free_typed (Γ := []) b) ≫
        ((sumIso (Φ := signature.Instr) Bit (BitTags K)).hom ≫ coprod.map (𝟙 _) (toStatesN K)) =
      ofRegion (caseValueBranches (act_typed K (b.toAct false)) (act_typed K (b.toAct true))) ≫
        (sumIso (Φ := signature.Instr) Bit (States K)).hom
  | .exit => by
    have retK : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr)
        [Silmaril.coprod Bit (States K)] := .br rfl (.inl (.var rfl))
    have a : ofRegion (nleaf_free_typed (Γ := []) (NLeaf.exit (K := K))) =
        coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (BitTags K)).inv :=
      (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))
    have b' : ofRegion retK = coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv :=
      (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))
    have c : ofRegion (caseValueBranches (act_typed K (.ret false)) (act_typed K (.ret true))) = ofRegion retK :=
      (bit_eta retK).symm
    rw [a]
    refine Eq.trans ?_ (congrArg (· ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) (c.trans b')).symm
    simp
  | .goto j => by
    have a : ofRegion (nleaf_free_typed (Γ := []) (NLeaf.goto j)) =
        ofRegion (bitTag_typed j) ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (BitTags K)).inv) :=
      br_inr (bitTag_value (Γ := []) j)
    have b' : ofRegion (goVarK_typed j) =
        ofRegion (rowState_typed j) ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
      br_inr (injTm_typed (.inl (.var (i := 0) rfl)) K j)
    rw [a]
    refine Eq.trans ?_ (congrArg (· ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom)
      ((goVarK_eta j).symm.trans b')).symm
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, coprod.inr_map]
    rw [← Category.assoc, toStatesN_tag]

/-! ## The step equation of every row -/

/-- The capture-free row of every block of every table, with its tags
sent to states, is the row of the router table. Default Paper. -/
theorem nstep (d : NTable K) (i : Fin (K + 1)) :
    ofRegion (d.free_typed i) ≫
        ((sumIso (Φ := signature.Instr) Bit (BitTags K)).hom ≫ coprod.map (𝟙 _) (toStatesN K)) =
      (ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed i)) ≫
        (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  have hL := nleaf_free_typed (Γ := []) (d.branch i false)
  have hR := nleaf_free_typed (Γ := []) (d.branch i true)
  have route := routerRoute_typed K (d.act i)
  have hF := (ofRegion_congr (free_as_ask d i) (d.free_typed i) (askCase_typed (d.label i) hL hR)).trans
    (ask_factor (d.label i) hL hR)
  have hP : ofRegion (labelPoll (d.label i)).program.typed.packExits =
      ofRegion (askPair_typed (d.label i)) ≫ ofRegion (caseValueBranches brInl_typed brInrInl_typed) :=
    ask_factor (d.label i) brInl_typed brInrInl_typed
  have hRow : ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed i) =
      ofRegion (askPair_typed (d.label i)) ≫
        ofRegion (caseValueBranches (seqValueBranches brInl_typed route) (seqValueBranches brInrInl_typed route)) :=
    (row_pollK (d.label i) (d.act i)).trans
      ((ofRegion_comp (labelPoll (d.label i)).program.typed.packExits route _).symm.trans
        ((congrArg (· ≫ ofRegion route) hP).trans ((Category.assoc _ _ _).trans
          (congrArg (ofRegion (askPair_typed (d.label i)) ≫ ·) (case_seq_arrow brInl_typed brInrInl_typed route)))))
  rw [hF, hRow, ← coprod_desc_ofRegion hL hR,
    ← coprod_desc_ofRegion (seqValueBranches brInl_typed route) (seqValueBranches brInrInl_typed route),
    route_leftK (d.act i), route_rightK (d.act i)]
  simp only [Category.assoc, coprod.desc_comp]
  rw [nleaf_post (d.branch i false), nleaf_post (d.branch i true)]

/-! ## Every table of the grammar -/

/-- The certificate of every table. -/
noncomputable def ntableCert (d : NTable K) : TagCert d.entry_typed d.blocks_typed d.router d.start :=
  ncert d (nstep d)

theorem nbitPointed (d : NTable K) :
    BitPointed d.source (fun i => some (d.label i)) d.act (fun _ => d.start) :=
  cert_bitPointed (label := fun i => some (d.label i)) (act := d.act) (ntableCert d)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem ncomplete (d : NTable K) (d' : NTable K') :
    Eqv false [Bit] d.source d'.source [Bit] ↔ Valid d.source_typed.hasType d'.source_typed.hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) d.source_typed d'.source_typed
    (nbitPointed d) (nbitPointed d')

theorem nbisim (d : NTable K) (d' : NTable K') :
    Eqv false [Bit] d.source d'.source [Bit] ↔
      ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → d.label x = d'.label y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧ R d.start d'.start :=
  (cert_eqv_iff_entered (ntableCert d) (ntableCert d')).trans
    (Router.labels_eqv_iff d.label d.act d'.label d'.act d.start d'.start)

end Step

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
