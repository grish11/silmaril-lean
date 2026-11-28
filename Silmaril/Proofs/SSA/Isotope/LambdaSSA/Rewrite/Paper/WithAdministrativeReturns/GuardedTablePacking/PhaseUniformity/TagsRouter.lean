module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PollRead

/-! # Tables with any number of blocks: erasing the capture and reaching a router table -/

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
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback (entry_route)

/-! ## Tags of any list of blocks -/

section AnyList

variable {X D P : Ty Empty}

local notation "Z" => ofType (Φ := signature.Instr) X

theorem freeDisp_cons {A : Ty Empty} {L : LCtx (Ty Empty)} (β : FreeRows (A :: L) (Silmaril.coprod D P)) :
    freeDisp (A :: L) β = (sumIso (Φ := signature.Instr) A (packedExitType L)).hom ≫
      coprod.desc (ofRegion (β (i := 0) (A := A) rfl).property ≫ (sumIso (Φ := signature.Instr) D P).hom)
        (freeDisp L (fun i B h => β (i := i + 1) (A := B) h)) := rfl

theorem tagArg_value {L : LCtx (Ty Empty)} {i : Nat} {A : Ty Empty} (h : At L i A) :
    Tm.BranchValue [A] (packedExitArg i (.var 0) : Tm signature.Instr) (packedExitType L) := by
  cases tagAt_typed (L := L) h with
  | br ho hv =>
    cases Option.some.inj ho
    exact hv

theorem tag_zero {A : Ty Empty} {L : LCtx (Ty Empty)} :
    ofRegion (tagAt_typed (L := A :: L) (i := 0) (A := A) rfl) =
      coprod.inl ≫ (sumIso (Φ := signature.Instr) A (packedExitType L)).inv :=
  (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id A)).trans (Category.id_comp _))

theorem tag_succ {A B : Ty Empty} {L : LCtx (Ty Empty)} {i : Nat} (h : At L i B) :
    ofRegion (tagAt_typed (L := A :: L) (i := i + 1) (A := B) h) =
      ofRegion (tagAt_typed h) ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) A (packedExitType L)).inv) :=
  br_inr (tagArg_value h)

/-- At the tag of a block, the step on the tags is the row of that block. -/
theorem tag_free : ∀ (L : LCtx (Ty Empty)) (β : FreeRows L (Silmaril.coprod D P)) {i : Nat} {A : Ty Empty}
    (h : At L i A),
    ofRegion (tagAt_typed h) ≫ freeDisp L β = ofRegion (β h).property ≫ (sumIso (Φ := signature.Instr) D P).hom
  | [], _, i, A, h => by simp [At] at h
  | A' :: L, β, 0, A, h => by
    obtain rfl : A' = A := Option.some.inj h
    rw [freeDisp_cons, tag_zero]
    simp
  | A' :: L, β, i + 1, A, h => by
    have ih := tag_free L (fun i B h => β (i := i + 1) (A := B) h) (show At L i A from h)
    rw [freeDisp_cons, tag_succ (A := A') (show At L i A from h)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
    exact ih

/-- Two arrows out of the tags are equal when they agree at every tag. -/
theorem tags_ext : ∀ (L : LCtx (Ty Empty)) {W : Paper.TypeCategory (τ := Ty Empty) signature.Instr}
    {f g : ofType (Φ := signature.Instr) (packedExitType L) ⟶ W},
    (∀ ⦃i : Nat⦄ ⦃A : Ty Empty⦄ (hi : At L i A),
      ofRegion (tagAt_typed hi) ≫ f = ofRegion (tagAt_typed hi) ≫ g) →
      f = g
  | [], _, f, g, _ => (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext f g
  | A :: L, W, f, g, h => by
    have h0 := h (i := 0) (A := A) rfl
    rw [tag_zero] at h0
    have hs : (coprod.inr ≫ (sumIso (Φ := signature.Instr) A (packedExitType L)).inv) ≫ f =
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) A (packedExitType L)).inv) ≫ g :=
      tags_ext L (fun i B hi => by
        have hi' := h (i := i + 1) (A := B) hi
        rw [tag_succ (A := A) hi] at hi'
        simpa only [Category.assoc] using hi')
    rw [← cancel_epi (sumIso (Φ := signature.Instr) A (packedExitType L)).inv]
    apply coprod.hom_ext
    · simpa only [Category.assoc] using h0
    · simpa only [Category.assoc] using hs

/-! ## Erasing a captured input from a dispatcher of any size -/

theorem lift_row_gen {A : Ty Empty} {β : Region signature.Instr} (hβ : ValueBranches [A] β [Silmaril.coprod D P]) :
    whiskerLeft Z (ofRegion hβ ≫ (sumIso (Φ := signature.Instr) D P).hom) ≫
        ((leftCoproductComparisonIso Z (ofType D) (ofType P)).inv ≫
          coprod.map (productSnd Z (ofType D)) (𝟙 (tensorObj Z (ofType P)))) =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P))) ≫
        (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom := by
  rw [whiskerLeft_comp, whiskerLeft_ofRegion, Category.assoc, ← dropCase_arrow, ← Category.assoc,
    ofRegion_comp (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P))
      (seqValueBranches (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P)))]

theorem lift_dead_gen {dR : Region signature.Instr}
    (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D (Silmaril.product X P)]) :
    whiskerLeft Z ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P)) ≫
        ((leftCoproductComparisonIso Z (ofType D) (ofType P)).inv ≫
          coprod.map (productSnd Z (ofType D)) (𝟙 (tensorObj Z (ofType P)))) =
      ofRegion (seqValueBranches (productSndBranches X Silmaril.empty) hd) ≫
        (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom := by
  obtain ⟨k, hk, ek⟩ := Paper.TypeCategory.exists_ofRegion
    ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P) ≫
      (sumIso (Φ := signature.Instr) D P).inv)
  have e : (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P) =
      ofRegion hk ≫ (sumIso (Φ := signature.Instr) D P).hom := by
    rw [← ek, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [e, lift_row_gen hk]
  exact congrArg (· ≫ (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom)
    (tensor_empty_ext (seqValueBranches (whiskerLeftRegion_typed X hk) (dropCase_typed (X := X) (B := D) (A := P)))
      (seqValueBranches (productSndBranches X Silmaril.empty) hd))

/-- A captured dispatcher of any number of rows, each the capture-free row
of its block whiskered by the captured input and followed by `dropCase`,
is the whiskered step on the tags followed by the dropping tail. -/
theorem disp_lift : ∀ (L : LCtx (Ty Empty))
    (rows : ∀ i : Fin L.length, {r : Region signature.Instr //
      ValueBranches [Silmaril.product X (L.get i)] r [Silmaril.coprod D (Silmaril.product X P)]})
    (β : FreeRows L (Silmaril.coprod D P))
    (_ : ∀ i : Fin L.length, ofRegion (rows i).property =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X (β (atGet L i)).property)
        (dropCase_typed (X := X) (B := D) (A := P)))),
    ofRegion (dispatcherRep X L rows).property ≫ (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom =
      (whiskerLeft Z (freeDisp L β) ≫ (leftCoproductComparisonIso Z (ofType D) (ofType P)).inv) ≫
        coprod.map (productSnd Z (ofType D)) (𝟙 (tensorObj Z (ofType P)))
  | [], _, _, _ =>
    ((Category.assoc _ _ _).trans (lift_dead_gen (X := X) (D := D) (P := P)
      (emptyDispatchRep (Φ := signature.Instr) (Silmaril.coprod D (Silmaril.product X P))).property)).symm
  | A :: L, rows, β, e => by
    have ih := disp_lift L (fun i => rows i.succ) (fun i B h => β (i := i + 1) (A := B) h) (fun i => e i.succ)
    have hrec := (dispatcherRep X L (fun i => rows i.succ)).property
    have hcase := caseValueBranches (rows 0).property hrec
    have hdis := distributorRegion_typed (Φ := signature.Instr) X A (packedExitType L)
    have left : ofRegion (dispatcherRep X (A :: L) rows).property ≫
        (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom =
        (ofRegion (τ := Ty Empty) hdis ≫ (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A)
          (Silmaril.product X (packedExitType L))).hom) ≫
          coprod.desc (ofRegion (rows 0).property ≫ (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom)
            (ofRegion hrec ≫ (sumIso (Φ := signature.Instr) D (Silmaril.product X P)).hom) := by
      have c : ofRegion (dispatcherRep X (A :: L) rows).property = ofRegion hdis ≫ ofRegion hcase :=
        (ofRegion_comp hdis hcase (seqValueBranches hdis hcase)).symm
      rw [c, ← coprod_desc_ofRegion (rows 0).property hrec]
      simp only [Category.assoc, coprod.desc_comp]
      rfl
    rw [left, ih, e 0, ← lift_row_gen (β (atGet (A :: L) 0)).property, freeDisp_cons, whisker_sum]
    simp only [Category.assoc, coprod.desc_comp]

/-- Such a dispatcher iterates as the step on the tags after the captured
input is dropped. Default Paper, for any number of rows. -/
theorem disp_drop (L : LCtx (Ty Empty))
    (rows : ∀ i : Fin L.length, {r : Region signature.Instr // ValueBranches [Silmaril.product X (L.get i)] r
      [Silmaril.coprod D (Silmaril.product X (packedExitType L))]})
    (β : FreeRows L (Silmaril.coprod D (packedExitType L)))
    (e : ∀ i : Fin L.length, ofRegion (rows i).property =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X (β (atGet L i)).property)
        (dropCase_typed (X := X) (B := D) (A := packedExitType L)))) :
    iterate (ofRegion (dispatcherRep X L rows).property ≫
        (sumIso (Φ := signature.Instr) D (Silmaril.product X (packedExitType L))).hom) =
      productSnd Z (ofType (packedExitType L)) ≫ iterate (freeDisp L β) := by
  rw [disp_lift L rows β e]
  exact iterate_projected_whiskerLeft Z (freeDisp L β)

/-- The packed readback of a table with any number of blocks whose rows
thread the captured input without using it, entered at a tag, is the
capture-free loop on the tags entered at that tag. Default Paper. -/
theorem readback_erase {n : Nat} (R : Fin n → Ty Empty) {e : Region signature.Instr}
    {blocks : Fin n → Region signature.Instr} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (β : FreeRows (List.ofFn R) (Silmaril.coprod D (packedExitType (List.ofFn R))))
    (hrows : ∀ j, ofRegion (orderedRow R hb j).property =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X (β (atGet _ j)).property)
        (dropCase_typed (X := X) (B := D) (A := packedExitType (List.ofFn R)))))
    {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t (packedExitType (List.ofFn R)))
    (hentry : ofRegion (entry_route R he) =
      ofRegion (r := .br 0 (.inr (.pair (.var 0) t)))
        (.br (L := [Silmaril.coprod D (Silmaril.product X (packedExitType (List.ofFn R)))]) rfl
          (.inr (.pair (.var rfl) ht)))) :
    ofRegion (packedReadbackRep R he hb).property =
      ofRegion (r := .br 0 t) (.br rfl ht) ≫ iterate (freeDisp (List.ofFn R) β) := by
  have hdisp := (dispatcherRep X (List.ofFn R) (orderedRow R hb)).property
  have hloop := SyntacticCategory.iterateRegion_valueBranches hdisp
  have ha : Tm.BranchValue [X] (.pair (.var 0) t : Tm signature.Instr)
      (Silmaril.product X (packedExitType (List.ofFn R))) := .pair (.var rfl) ht
  have hbr : ValueBranches [X] (.br 0 (.pair (.var 0) t) : Region signature.Instr)
      [Silmaril.product X (packedExitType (List.ofFn R))] := .br rfl ha
  have hid : ValueBranches [D] (.br 0 (.var 0) : Region signature.Instr) [D] := .br rfl (.var rfl)
  have shape : ofRegion (packedReadbackRep R he hb).property =
      ofRegion (entry_route R he) ≫ ofRegion (caseValueBranches hid hloop) :=
    (ofRegion_comp (entry_route R he) (caseValueBranches hid hloop)
      (seqValueBranches (entry_route R he) (caseValueBranches hid hloop))).symm
  have s₀ := ofRegion_comp (ValueBranches.br (ℓ := 0)
    (L := [Silmaril.coprod D (Silmaril.product X (packedExitType (List.ofFn R)))]) rfl (.inr ha))
    (caseValueBranches hid hloop) (seqValueBranches (ValueBranches.br (ℓ := 0)
    (L := [Silmaril.coprod D (Silmaril.product X (packedExitType (List.ofFn R)))]) rfl (.inr ha))
    (caseValueBranches hid hloop))
  have s₁ := case_inr_arrow ha hid hloop
  have s₂ := ofRegion_comp hbr hloop (seqValueBranches hbr hloop)
  have s₃ := iterate_exact hdisp
  have s₄ := disp_drop (List.ofFn R) (orderedRow R hb) β hrows
  have hbody : Region.HasType [packedExitType (List.ofFn R), X, X] (.br 0 (.var 0) : Region signature.Instr)
      [packedExitType (List.ofFn R)] := (ValueBranches.br (ℓ := 0) rfl (.var rfl)).hasType
  have s₅ : ofRegion hbr ≫ productSnd Z (ofType (packedExitType (List.ofFn R))) =
      ofRegion (r := .br 0 t) (.br rfl ht) :=
    (ofRegion_comp hbr (productSndBranches X (packedExitType (List.ofFn R)))
      (seqValueBranches hbr (productSndBranches X (packedExitType (List.ofFn R))))).trans
      ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
        (.productBeta (.let₂Beta (A := X) (B := packedExitType (List.ofFn R)) (.var rfl) ht hbody)))
  exact shape.trans ((congrArg (· ≫ ofRegion (caseValueBranches hid hloop)) hentry).trans
    (s₀.trans (s₁.trans (s₂.symm.trans ((congrArg (ofRegion hbr ≫ ·) (s₃.symm.trans s₄)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ iterate (freeDisp (List.ofFn R) β)) s₅)))))))

end AnyList

/-! ## From the tags of `K + 1` Bit blocks to a router table with `K + 1` rows -/

section Router

variable {K : Nat}

/-- From a packed state at row `i` to the tag of block `i`. -/
def untagK (i : Fin (K + 1)) : Region signature.Instr :=
  seqRegion (unpackExits [Bit]) (.br 0 (packedExitArg i.val (.var 0)))

theorem untagK_typed (i : Fin (K + 1)) : ValueBranches [State] (untagK i) [BitTags K] :=
  seqRegion_typed unpack_typed (bitTag_typed i)

noncomputable def toTagsK (K : Nat) : ofType (Φ := signature.Instr) (States K) ⟶ ofType (BitTags K) :=
  ofRegion (dispatch_typed K (untagK_typed (K := K)))

theorem rowState_arrow (i : Fin (K + 1)) :
    ofRegion (rowState_typed i) = ofRegion bitState_typed ≫ injArr K i :=
  injOf_eq (.inl (.var rfl)) K i

theorem state_toTagsK (i : Fin (K + 1)) : ofRegion (rowState_typed i) ≫ toTagsK K = ofRegion (bitTag_typed i) :=
  (congrArg (· ≫ toTagsK K) (rowState_arrow i)).trans ((Category.assoc _ _ _).trans
    ((congrArg (ofRegion bitState_typed ≫ ·) (inj_dispatch K untagK_typed i)).trans
      ((congrArg (ofRegion bitState_typed ≫ ·)
        (ofRegion_comp unpack_typed (bitTag_typed i) (untagK_typed i)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ ofRegion (bitTag_typed i)) pack_unpack).trans (Category.id_comp _))))))

variable {e : Region signature.Instr} {blocks : Fin (K + 1) → Region signature.Instr}
  {he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
  {hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
  {t : Router K} {s : Fin (K + 1)}

/-- A tag sent to a state and back is the tag. -/
theorem cert_roundtrip (c : TagCert he hb t s) : c.toStates ≫ toTagsK K = 𝟙 _ := by
  apply tags_ext
  intro i A hi
  obtain rfl := eq_of_atBit hi
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ toTagsK K) (c.tags ⟨i, lt_of_atBit hi⟩)).trans
    ((state_toTagsK ⟨i, lt_of_atBit hi⟩).trans (Category.comp_id _).symm))

theorem cert_free (c : TagCert he hb t s) (i : Fin (K + 1)) :
    ofRegion (bitTag_typed i) ≫ freeDisp _ (freeOfBlocks c.free c.free_typed) =
      ofRegion (c.free_typed i) ≫ (sumIso (Φ := signature.Instr) Bit (BitTags K)).hom :=
  tag_free _ (freeOfBlocks c.free c.free_typed) (atBit i)

/-- The step on the tags, conjugated by the two maps, is the dispatcher
step of the router table. -/
theorem cert_conj (c : TagCert he hb t s) :
    toTagsK K ≫ (freeDisp _ (freeOfBlocks c.free c.free_typed) ≫ coprod.map (𝟙 _) c.toStates) =
      ofRegion (dispatch_typed K t.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  apply inj_ext K
  intro i
  apply state_ext_bit
  have a : (ofRegion bitState_typed ≫ injArr K i) ≫ toTagsK K = ofRegion (bitTag_typed i) :=
    (congrArg (· ≫ toTagsK K) (rowState_arrow i).symm).trans (state_toTagsK i)
  have t₁ : ((ofRegion bitState_typed ≫ injArr K i) ≫ toTagsK K) ≫
      (freeDisp _ (freeOfBlocks c.free c.free_typed) ≫ coprod.map (𝟙 _) c.toStates) =
      (ofRegion bitState_typed ≫ ofRegion (t.rows_typed i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom :=
    (congrArg (· ≫ (freeDisp _ (freeOfBlocks c.free c.free_typed) ≫ coprod.map (𝟙 _) c.toStates)) a).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coprod.map (𝟙 _) c.toStates) (cert_free c i)).trans
        ((Category.assoc _ _ _).trans (c.step i))))
  have t₂ : (ofRegion bitState_typed ≫ injArr K i) ≫
      (ofRegion (dispatch_typed K t.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) =
      (ofRegion bitState_typed ≫ ofRegion (t.rows_typed i)) ≫
        (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
    rw [← inj_dispatch K t.rows_typed i]
    simp only [Category.assoc]
  simpa only [Category.assoc] using t₁.trans t₂.symm

theorem cert_loop (c : TagCert he hb t s) :
    iterate (ofRegion (dispatch_typed K t.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) =
      toTagsK K ≫ iterate (freeDisp _ (freeOfBlocks c.free c.free_typed)) := by
  have roll := iterate_roll (toTagsK K)
    (freeDisp _ (freeOfBlocks c.free c.free_typed) ≫ coprod.map (𝟙 _) c.toStates)
  have back : (freeDisp _ (freeOfBlocks c.free c.free_typed) ≫ coprod.map (𝟙 _) c.toStates) ≫
      coprod.map (𝟙 _) (toTagsK K) = freeDisp _ (freeOfBlocks c.free c.free_typed) := by
    simp only [Category.assoc, coprod.map_map, Category.comp_id, cert_roundtrip c, coprod.map_id_id]
  rw [← cert_conj c, roll, back]

/-- The packed readback is the router table entered at the start row, on
the input as its Bit. Default Paper. -/
theorem cert_readback (c : TagCert he hb t s) :
    ofRegion (packedReadbackRep (fun _ : Fin (K + 1) => Bit) he hb).property =
      ofRegion bitState_typed ≫ ofRegion (t.entered_typed s) :=
  (readback_erase (X := Bit) (D := Bit) (fun _ : Fin (K + 1) => Bit) he hb (freeOfBlocks c.free c.free_typed)
    c.rows (tagArg_value (atBit s)) c.entry).trans
    ((congrArg (· ≫ iterate (freeDisp _ (freeOfBlocks c.free c.free_typed))) (state_toTagsK s).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (ofRegion (rowState_typed s) ≫ ·)
          ((cert_loop c).symm.trans (iterate_exact (dispatch_typed K t.rows_typed)))).trans
          ((congrArg (· ≫ ofRegion (dispatchLoop_typed t.rows_typed)) (rowState_arrow s)).trans
            ((Category.assoc _ _ _).trans (congrArg (ofRegion bitState_typed ≫ ·)
              (dispatchEntered_arrow t.rows_typed s).symm))))))

theorem cert_typed (he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]))
    (hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])) :
    ValueBranches [Bit] (.cfg e (K + 1) blocks) [Bit] :=
  .cfg (fun _ : Fin (K + 1) => Bit) he hb

/-- The table is the router table entered at the start row, in the
table-packing quotient. -/
theorem cert_source (c : TagCert he hb t s) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] (.cfg e (K + 1) blocks)
      (seqRegion (.br 0 (.inl (.var 0))) (t.entered s)) [Bit] :=
  (Paper.WithAdministrativeReturns.WithGuardedTablePacking.pack false (fun _ : Fin (K + 1) => Bit) he hb).trans
    (.paper ((Paper.TypeCategory.ofRegion_eq_iff (packedReadbackRep (fun _ : Fin (K + 1) => Bit) he hb).property
      (seqRegion_typed bitState_typed (t.entered_typed s))).mp
      ((cert_readback c).trans (ofRegion_comp bitState_typed (t.entered_typed s) _))))

theorem q_cert_source (c : TagCert he hb t s) :
    QLit (cert_typed he hb) = QLit bitState_typed ≫ QLit (t.entered_typed s) :=
  ((Paper.Extension.Singleton.ofRegion_eq_iff N (cert_typed he hb)
    (seqRegion_typed bitState_typed (t.entered_typed s))).2
    (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
      (cert_source c))).trans (q_comp bitState_typed (t.entered_typed s))

/-- The certificate at the two constant inputs. -/
theorem cert_bitPointed {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
    (c : TagCert he hb (Router.ofSpin label act) s) :
    BitPointed (.cfg e (K + 1) blocks) label act (fun _ => s) := by
  intro q
  have hE := (Router.ofSpin label act).entered_typed s
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q (cert_typed he hb))
    (constEntry_typed q hE)).1
  exact (q_comp (bitU_typed q) (cert_typed he hb)).trans
    ((congrArg (QLit (bitU_typed q) ≫ ·) (q_cert_source c)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ QLit hE) (((π).map_comp _ _).symm.trans (congrArg (π).map (const_arrow q).symm))).trans
          (q_comp (const_typed q) hE).symm)))

/-- Two tables with certificates are equal at the source entry exactly
when their router tables are equal at the start rows. -/
theorem cert_eqv_iff_entered {K' : Nat} {e' : Region signature.Instr}
    {blocks' : Fin (K' + 1) → Region signature.Instr}
    {he' : ValueBranches [Bit] e' (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
    {hb' : ∀ i, ValueBranches [Bit, Bit] (blocks' i) (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
    {t' : Router K'} {s' : Fin (K' + 1)} (c : TagCert he hb t s) (c' : TagCert he' hb' t' s') :
    Eqv false [Bit] (.cfg e (K + 1) blocks) (.cfg e' (K' + 1) blocks') [Bit] ↔
      Eqv false [State] (t.entered s) (t'.entered s') [Bit] := by
  have hE := t.entered_typed s
  have hE' := t'.entered_typed s'
  constructor
  · intro h
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N hE hE').1
    apply q_state_ext hE hE'
    exact (q_comp bitState_typed hE).trans ((q_cert_source c).symm.trans
      (((Paper.Extension.Singleton.ofRegion_eq_iff N (cert_typed he hb) (cert_typed he' hb')).2 h).trans
        ((q_cert_source c').trans (q_comp bitState_typed hE').symm)))
  · intro h
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N (cert_typed he hb) (cert_typed he' hb')).1
    exact (q_cert_source c).trans ((congrArg (QLit bitState_typed ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N hE hE').2 h)).trans (q_cert_source c').symm)

end Router

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two tables with certificates in tidy router tables are equal at the
source entry exactly when they are valid in every supported model. -/
theorem cert_complete {K K' : Nat} {e e' : Region signature.Instr} {blocks : Fin (K + 1) → Region signature.Instr}
    {blocks' : Fin (K' + 1) → Region signature.Instr}
    {he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
    {hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
    {he' : ValueBranches [Bit] e' (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
    {hb' : ∀ i, ValueBranches [Bit, Bit] (blocks' i) (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
    {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
    {label' : Fin (K' + 1) → Option Bool} {act' : Fin (K' + 1) → Bool → Bool → Act K'}
    {s : Fin (K + 1)} {s' : Fin (K' + 1)} (ht : Tidy label act) (ht' : Tidy label' act')
    (c : TagCert he hb (Router.ofSpin label act) s) (c' : TagCert he' hb' (Router.ofSpin label' act') s') :
    Eqv false [Bit] (.cfg e (K + 1) blocks) (.cfg e' (K' + 1) blocks') [Bit] ↔
      Valid (cert_typed he hb).hasType (cert_typed he' hb').hasType :=
  bit_source_complete ht ht' (cert_typed he hb) (cert_typed he' hb') (cert_bitPointed c) (cert_bitPointed c')

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
