module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Cycle3

/-! # Rows, entry and tag map of the grammar, for every size -/

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

/-! ## A tag under renaming and substitution -/

/-- A tag built on the newest variable is unchanged by a renaming that
fixes that variable. -/
theorem packedExitArg_rename0 : ∀ (j : Nat) (ρ : Nat → Nat), ρ 0 = 0 →
    (packedExitArg j (.var 0) : Tm signature.Instr).rename ρ = packedExitArg j (.var 0)
  | 0, _, h => congrArg (fun n => (Tm.inl (Tm.var n) : Tm signature.Instr)) h
  | j + 1, ρ, h => congrArg Tm.inr (packedExitArg_rename0 j ρ h)

/-- And by a substitution that fixes that variable. -/
theorem packedExitArg_subst0 : ∀ (j : Nat) (θ : Nat → Tm signature.Instr), θ 0 = .var 0 →
    (packedExitArg j (.var 0) : Tm signature.Instr).subst θ = packedExitArg j (.var 0)
  | 0, _, h => congrArg Tm.inl h
  | j + 1, θ, h => congrArg Tm.inr (packedExitArg_subst0 j θ h)

theorem ofRegion_congr {X Y : Ty Empty} {r r' : Region signature.Instr} (e : r = r')
    (h : ValueBranches [X] r [Y]) (h' : ValueBranches [X] r' [Y]) : ofRegion h = ofRegion h' := by
  subst e
  rfl

section Grammar

variable {K : Nat}

/-! ## The leaves of a readback row, for a variable index -/

/-- A capture-free leaf, whiskered by the captured input and followed by
`dropCase`. -/
def liftLeafN (x : Region signature.Instr) : Region signature.Instr :=
  ((x.renameVars (lift (lift (Nat.succ ∘ Nat.succ)))).lsubst
      (liftLSubstVars (fun _ => .br 0 (.pair (.var 2) (.var 0))))).lsubst
    (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => dropCase.renameVars (lift Nat.succ)))))

/-- What the readback does to a leaf: the routed exit, under the binders
of the row. -/
def rbShape (r : Region signature.Instr) : Region signature.Instr :=
  ((r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0))).renameVars (lift (lift (lift Nat.succ)))

theorem carry_exit :
    (carryExit 1 (K + 1) (K + 1) : Region signature.Instr) = .br 0 (.inl (.var 0)) := by
  simp [carryExit]

theorem carry_block (c : Nat) (j : Fin (K + 1)) :
    (carryExit c (K + 1) j.val : Region signature.Instr) =
      .br 0 (.inr (.pair (.var (c + 1)) (packedExitArg j.val (.var 0)))) := by
  simp [carryExit, j.isLt]

theorem tag_shape (j : Fin (K + 1)) :
    (((packedExitArg j.val (.var 0) : Tm signature.Instr).rename (lift Nat.succ)).subst
      (Tm.singleSubst (.var 0))).rename (lift (lift (lift Nat.succ))) = packedExitArg j.val (.var 0) :=
  (congrArg (fun u : Tm signature.Instr => (u.subst (Tm.singleSubst (.var 0))).rename (lift (lift (lift Nat.succ))))
    (packedExitArg_rename0 j.val (lift Nat.succ) rfl)).trans
    ((congrArg (fun u : Tm signature.Instr => u.rename (lift (lift (lift Nat.succ))))
      (packedExitArg_subst0 j.val (Tm.singleSubst (.var 0)) rfl)).trans
      (packedExitArg_rename0 j.val (lift (lift (lift Nat.succ))) rfl))

/-- A leaf of a readback row is the capture-free leaf in lifted form, for
every leaf and every size. -/
theorem nleaf_lift : (b : NLeaf K) →
    Paper.Eqv [Bit, Bit, Bit, Silmaril.product Bit Bit] (liftLeafN b.free)
      (rbShape (carryExit 1 (K + 1) b.idx)) [Silmaril.coprod Bit (Silmaril.product Bit (BitTags K))]
  | .exit => by
    have e : rbShape (carryExit 1 (K + 1) (NLeaf.exit (K := K)).idx : Region signature.Instr) =
        .br 0 (.inl (.var 0)) := congrArg rbShape carry_exit
    rw [e]
    exact drop_inl (X := Bit) (A := BitTags K) (i := 2) rfl (.var (i := 0) rfl)
  | .goto j => by
    have e₁ : liftLeafN (NLeaf.goto j).free =
        .let₂ (.pair (.var 2) (.inr (packedExitArg j.val (.var 0))))
          (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0))))) :=
      congrArg (fun t : Tm signature.Instr => Region.let₂ (.pair (.var 2) (.inr t))
        (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0))))))
        (packedExitArg_rename0 j.val (lift (lift (Nat.succ ∘ Nat.succ))) rfl)
    have e₂ : rbShape (carryExit 1 (K + 1) (NLeaf.goto j).idx : Region signature.Instr) =
        .br 0 (.inr (.pair (.var 2) (packedExitArg j.val (.var 0)))) :=
      (congrArg rbShape (carry_block 1 j)).trans
        (congrArg (fun t : Tm signature.Instr => Region.br 0 (.inr (.pair (.var 2) t))) (tag_shape j))
    rw [e₁, e₂]
    exact drop_inr (X := Bit) (B := Bit) (i := 2) rfl (bitTag_value j)

/-! ## Every generated row, and the entry -/

/-- The readback row of every block of every table is its capture-free
row whiskered by the captured input and followed by `dropCase`. -/
theorem nrow_lift (d : NTable K) (i : Fin (K + 1)) :
    Paper.Eqv [Silmaril.product Bit Bit] (seqRegion (whiskerLeftRegion (d.free i)) dropCase)
      (Paper.RetainedLet.unpackBody ((d.blocks i).lsubst (carryExit 1 (K + 1))))
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags K))] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (nleaf_lift (d.branch i false))
      (nleaf_lift (d.branch i true)))

/-- An equation at a pair with a Bit holds at a pair with a type equal to Bit. -/
theorem eqv_cast {T : Ty Empty} (hT : T = Bit) {r s : Region signature.Instr} {L : LCtx (Ty Empty)}
    (h : Paper.Eqv [Silmaril.product Bit Bit] r s L) : Paper.Eqv [Silmaril.product Bit T] r s L := by
  subst hT
  exact h

/-- The same at the parameter type that the readback gives the row. -/
theorem nrow_cert (d : NTable K) (j : Fin (List.ofFn (fun _ : Fin (K + 1) => Bit)).length) :
    ofRegion (orderedRow (fun _ : Fin (K + 1) => Bit) d.blocks_typed j).property =
      ofRegion (seqValueBranches
        (whiskerLeftRegion_typed Bit ((freeOfBlocks d.free d.free_typed) (atGet _ j)).property)
        (dropCase_typed (X := Bit) (B := Bit) (A := BitTags K))) := by
  apply (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
  exact eqv_cast (eq_of_atBit (atGet _ j)) (nrow_lift d ⟨j.val, by simpa using j.isLt⟩).symm

/-- The routed entry is the start tag with the captured input. -/
theorem nentry (d : NTable K) :
    ofRegion (entry_route (fun _ : Fin (K + 1) => Bit) d.entry_typed) = ofRegion (entryTag_typed d.start) :=
  ofRegion_congr
    ((congrArg (fun r : Region signature.Instr => r.substVars (Tm.singleSubst (.var 0)))
      (carry_block 0 d.start)).trans
      (congrArg (fun u : Tm signature.Instr => Region.br 0 (.inr (.pair (.var 0) u)))
        (packedExitArg_subst0 d.start.val (Tm.singleSubst (.var 0)) rfl))) _ _

/-! ## The map from tags to states -/

theorem tagsFold_cons {A E : Ty Empty} {L : LCtx (Ty Empty)} (β : FreeRows (A :: L) E) :
    tagsFold (A :: L) β = (sumIso (Φ := signature.Instr) A (packedExitType L)).hom ≫
      coprod.desc (ofRegion (β (i := 0) (A := A) rfl).property)
        (tagsFold L (fun i B h => β (i := i + 1) (A := B) h)) := rfl

/-- At the tag of a block, the fold is the region of that block. -/
theorem tag_fold {E : Ty Empty} : ∀ (L : LCtx (Ty Empty)) (β : FreeRows L E) {i : Nat} {A : Ty Empty}
    (h : At L i A), ofRegion (tagAt_typed h) ≫ tagsFold L β = ofRegion (β h).property
  | [], _, i, A, h => by simp [At] at h
  | A' :: L, β, 0, A, h => by
    obtain rfl : A' = A := Option.some.inj h
    rw [tagsFold_cons, tag_zero]
    simp
  | A' :: L, β, i + 1, A, h => by
    have ih := tag_fold L (fun i B h => β (i := i + 1) (A := B) h) (show At L i A from h)
    rw [tagsFold_cons, tag_succ (A := A') (show At L i A from h)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
    exact ih

/-- The map from tags to states sends the tag of block `i` to row `i`,
for every size. -/
theorem toStatesN_tag (i : Fin (K + 1)) :
    ofRegion (bitTag_typed i) ≫ toStatesN K = ofRegion (rowState_typed i) :=
  tag_fold _ (freeOfBlocks (fun i => .br 0 (injTm K i (.inl (.var 0)))) (rowState_typed (K := K))) (atBit i)

/-! ## Capture erasure for every table, and the certificate from the step equations -/

/-- The packed readback of every table of the grammar is the capture-free
loop on its tags, entered at the start tag. Default Paper, every size. -/
theorem nreadback_tags (d : NTable K) :
    ofRegion (packedReadbackRep (fun _ : Fin (K + 1) => Bit) d.entry_typed d.blocks_typed).property =
      ofRegion (bitTag_typed d.start) ≫ iterate (freeDisp _ (freeOfBlocks d.free d.free_typed)) :=
  readback_erase (X := Bit) (D := Bit) (fun _ : Fin (K + 1) => Bit) d.entry_typed d.blocks_typed
    (freeOfBlocks d.free d.free_typed) (nrow_cert d) (tagArg_value (atBit d.start)) (nentry d)

/-- The certificate of a table, from the step equations of its rows. -/
noncomputable def ncert (d : NTable K) (h : Task.nStep d) :
    TagCert d.entry_typed d.blocks_typed d.router d.start where
  free := d.free
  free_typed := d.free_typed
  toStates := toStatesN K
  entry := nentry d
  rows := nrow_cert d
  tags := toStatesN_tag
  step := h

end Grammar

/-! ## Size three: the cycle through the uniform construction -/

theorem cycleN_source (l : Bool) : (cycleN l).source = cycleSource l := (cycleSource_eq l).symm

theorem toStates3_eq : toStatesN 2 = ofRegion toStates3.property :=
  tags_ext _ (fun i A hi => by
    obtain rfl := eq_of_atBit hi
    exact (toStatesN_tag ⟨i, lt_of_atBit hi⟩).trans (cyc_tags ⟨i, lt_of_atBit hi⟩).symm)

/-- The step equations of the cycle, from its fixed-size proof. -/
theorem cycleN_step (l : Bool) : Task.nStep (cycleN l) := fun i => by
  rw [toStates3_eq]
  exact cyc_step l i

section Conditional

variable {K K' : Nat}

theorem ntable_spin (d : NTable K) : Router.ofSpin (fun i => some (d.label i)) d.act = d.router := rfl

theorem nbitPointed (d : NTable K) (h : Task.nStep d) :
    BitPointed d.source (fun i => some (d.label i)) d.act (fun _ => d.start) :=
  cert_bitPointed (label := fun i => some (d.label i)) (act := d.act) (ncert d h)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem ncomplete (d : NTable K) (d' : NTable K') (h : Task.nStep d) (h' : Task.nStep d') :
    Eqv false [Bit] d.source d'.source [Bit] ↔ Valid d.source_typed.hasType d'.source_typed.hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) d.source_typed d'.source_typed
    (nbitPointed d h) (nbitPointed d' h')

end Conditional

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
