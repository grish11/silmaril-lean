module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PackedSource

/-! # A pair of Bits is the packed state of two rows -/

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

/-! ## Decoding then encoding, in default Paper -/

theorem state_ext_bit {Z : Paper.TypeCategory (τ := Ty Empty) signature.Instr}
    {f g : ofType (Φ := signature.Instr) State ⟶ Z}
    (h : ofRegion bitState_typed ≫ f = ofRegion bitState_typed ≫ g) : f = g :=
  state_hom_ext fun b => by
    rw [const_arrow, Category.assoc, h, ← Category.assoc]

theorem bit_decRow (c : Bool) :
    ofRegion bitState_typed ≫ ofRegion (pairDecRow_typed c) = ofRegion (pairLit_typed c) := by
  have red := case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr))
    (.var (i := 0) rfl) (pairLit_typed c) pairDead_typed
  have a := ofRegion_comp bitState_typed (pairDecRow_typed c)
    (seqValueBranches bitState_typed (pairDecRow_typed c))
  have b := (ofRegion_comp idBit (pairLit_typed c) (seqValueBranches idBit (pairLit_typed c))).symm
  exact a.symm.trans (red.trans (b.trans (by rw [ofRegion_id, Category.id_comp])))

theorem injBit_typed (c : Bool) :
    ValueBranches [Bit] (.br 0 (injTm 1 (pairIdx c) (.inl (.var 0))) : Region signature.Instr) [States 1] :=
  .br rfl (injTm_typed (.inl (.var rfl)) 1 (pairIdx c))

theorem injBit_arrow (c : Bool) : ofRegion (injBit_typed c) = ofRegion bitState_typed ≫ injArr 1 (pairIdx c) :=
  injOf_eq (.inl (.var rfl)) 1 (pairIdx c)

/-- Encoding a pair whose first Bit is a constant selects the row of that
constant. Product β and the native case on a constructor. -/
theorem enc_lit (c : Bool) :
    ofRegion (seqValueBranches (pairLit_typed c) pairEnc_typed) = ofRegion (injBit_typed c) := by
  apply (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
  have hbody : Region.HasType [Bit, Bit, Bit]
      (.case (.var 1) (.br 0 (.inl (.inl (.var 1)))) (.br 0 (.inr (.inl (.var 1)))) : Region signature.Instr)
      [States 1] :=
    (ValueBranches.case (A := Ty.unit) (B := Ty.unit) (.var rfl) (.br rfl (.inl (.inl (.var rfl))))
      (.br rfl (.inr (.inl (.var rfl))))).hasType
  have beta := Paper.Eqv.productBeta
    (ProductBeta.Step.let₂Beta (Γ := [Bit]) (a := litBit c) (b := (.var 0 : Tm signature.Instr))
      (litBit_typed c) (.var rfl) hbody)
  have hl : Region.HasType [U, Bit] (.br 0 (.inl (.inl (.var 1))) : Region signature.Instr) [States 1] :=
    (ValueBranches.br (ℓ := 0) rfl (.inl (.inl (.var rfl)))).hasType
  have hr : Region.HasType [U, Bit] (.br 0 (.inr (.inl (.var 1))) : Region signature.Instr) [States 1] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.inl (.var rfl)))).hasType
  cases c
  · have pick : Paper.Eqv [Bit] (.case (.inl .unit) (.br 0 (.inl (.inl (.var 1)))) (.br 0 (.inr (.inl (.var 1)))))
        (.let₁ .unit (.br 0 (.inl (.inl (.var 1)))) : Region signature.Instr) [States 1] :=
      .cfgEta (.native (.base (.caseInl .unit hl hr)))
    have bind : Paper.Eqv [Bit] (.let₁ .unit (.br 0 (.inl (.inl (.var 1)))))
        (.br 0 (.inl (.inl (.var 0))) : Region signature.Instr) [States 1] :=
      .cfgEta (.native (.base (.letBr .unit (.inl (.inl (.var rfl))) rfl)))
    exact beta.trans (pick.trans bind)
  · have pick : Paper.Eqv [Bit] (.case (.inr .unit) (.br 0 (.inl (.inl (.var 1)))) (.br 0 (.inr (.inl (.var 1)))))
        (.let₁ .unit (.br 0 (.inr (.inl (.var 1)))) : Region signature.Instr) [States 1] :=
      .cfgEta (.native (.base (.caseInr .unit hl hr)))
    have bind : Paper.Eqv [Bit] (.let₁ .unit (.br 0 (.inr (.inl (.var 1)))))
        (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) [States 1] :=
      .cfgEta (.native (.base (.letBr .unit (.inr (.inl (.var rfl))) rfl)))
    exact beta.trans (pick.trans bind)

/-- Decoding and then encoding is the identity on the packed state, in
default Paper. -/
theorem dec_enc :
    ofRegion pairDec_typed ≫ ofRegion pairEnc_typed = 𝟙 (ofType (Φ := signature.Instr) (States 1)) := by
  apply inj_ext 1
  intro i
  rw [← Category.assoc, inj_dispatch 1 (fun i => pairDecRow_typed (pairBit i)) i, Category.comp_id]
  apply state_ext_bit
  rw [← Category.assoc, bit_decRow,
    ofRegion_comp (pairLit_typed (pairBit i)) pairEnc_typed
      (seqValueBranches (pairLit_typed (pairBit i)) pairEnc_typed), enc_lit]
  match i with
  | 0 => exact injBit_arrow false
  | 1 => exact injBit_arrow true

/-! ## Encoding then decoding, with unit η -/

theorem inj_dec (c : Bool) :
    ofRegion (seqValueBranches (injBit_typed c) pairDec_typed) = ofRegion (pairLit_typed c) := by
  rw [← ofRegion_comp (injBit_typed c) pairDec_typed (seqValueBranches (injBit_typed c) pairDec_typed),
    injBit_arrow, Category.assoc, inj_dispatch 1 (fun i => pairDecRow_typed (pairBit i)) (pairIdx c)]
  cases c <;> exact bit_decRow _

/-- Unit η in a context: a returned value built on literal unit is the
value built on a unit variable. -/
theorem unit_fill {Γ : VCtx (Ty Empty)} {D : Ty Empty} {i : Nat} (hi : At Γ i U) (t : Tm signature.Instr)
    (ht : Tm.BranchValue (U :: Γ) t D) :
    Eqv false Γ ((Region.br 0 t).substVars (Tm.singleSubst .unit))
      ((Region.br 0 t).substVars (Tm.singleSubst (.var i))) [D] := by
  have e := Paper.Extension.Eqv.substVars (Δ := Γ) (θ := fun _ => (.var i : Tm signature.Instr)) unit_eta
    (fun k A h => by
      cases k with
      | zero =>
        cases h
        exact .var hi
      | succ k => cases h)
  exact Paper.Extension.Eqv.lsubstPost (σ := fun _ => .br 0 t) e (.br rfl .unit) (.br rfl (.var hi))
    (fun ℓ A hA => by
      cases ℓ with
      | zero =>
        cases hA
        exact (ValueBranches.br (ℓ := 0) rfl ht).hasType
      | succ ℓ => cases hA)

/-- Under the case on the first Bit, decoding the selected row rebuilds
the pair from the unit payload of the case and the second Bit. -/
theorem enc_arm_false :
    Eqv false [U, Bit, Bit, Pair]
      (((Region.br 0 (injTm 1 (pairIdx false) (.inl (.var 0)))).lsubst
        (fun _ => pairDec.renameVars (Silmaril.DeBruijn.lift Nat.succ))).substVars
          (fun _ => (.var 1 : Tm signature.Instr)))
      (.br 0 (.pair (.inl (.var 0)) (.var 1))) [Pair] := by
  have weak := Paper.Eqv.substVars (Δ := [U, Bit, Bit, Pair]) (θ := fun _ => (.var 1 : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (inj_dec false)) (fun i A h => by
      cases i with
      | zero =>
        cases h
        exact .var rfl
      | succ i => cases h)
  exact (Paper.Extension.Eqv.paper weak).trans
    (unit_fill (Γ := [U, Bit, Bit, Pair]) (i := 0) rfl (.pair (.inl (.var 0)) (.var 2))
      (.pair (.inl (.var rfl)) (.var rfl)))

theorem enc_arm_true :
    Eqv false [U, Bit, Bit, Pair]
      (((Region.br 0 (injTm 1 (pairIdx true) (.inl (.var 0)))).lsubst
        (fun _ => pairDec.renameVars (Silmaril.DeBruijn.lift Nat.succ))).substVars
          (fun _ => (.var 1 : Tm signature.Instr)))
      (.br 0 (.pair (.inr (.var 0)) (.var 1))) [Pair] := by
  have weak := Paper.Eqv.substVars (Δ := [U, Bit, Bit, Pair]) (θ := fun _ => (.var 1 : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (inj_dec true)) (fun i A h => by
      cases i with
      | zero =>
        cases h
        exact .var rfl
      | succ i => cases h)
  exact (Paper.Extension.Eqv.paper weak).trans
    (unit_fill (Γ := [U, Bit, Bit, Pair]) (i := 0) rfl (.pair (.inr (.var 0)) (.var 2))
      (.pair (.inr (.var rfl)) (.var rfl)))

/-- Encoding and then decoding is the identity on pairs. The native case
on a variable, product η, and unit η for the first Bit. -/
theorem enc_dec : Retracts Pair pairEnc pairDec := by
  have split : Paper.Eqv [Bit, Bit, Pair]
      (.case (.var 1) (.br 0 (.pair (.inl (.var 0)) (.var 1))) (.br 0 (.pair (.inr (.var 0)) (.var 1))))
      (.br 0 (.pair (.var 1) (.var 0)) : Region signature.Instr) [Pair] :=
    .cfgEta (.native (SubstitutionEquiv.caseValue (Γ := [Bit, Bit, Pair]) (A := U) (B := U)
      (a := (.var 1 : Tm signature.Instr)) (.var rfl)
      (ValueBranches.br (ℓ := 0) (Γ := [Bit, Bit, Bit, Pair]) (L := [Pair]) rfl
        (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))).hasType))
  have eta : Paper.Eqv [Pair] (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var 0) : Region signature.Instr) [Pair] :=
    .productEta (.let₂Eta (i := 0) (ℓ := 0) (A := Bit) (B := Bit) rfl rfl)
  exact (Paper.Extension.Eqv.let₂ (A := Bit) (B := Bit) (.var rfl)
    ((Paper.Extension.Eqv.case (A := U) (B := U) (.var rfl) enc_arm_false enc_arm_true).trans
      (.paper split))).trans (.paper eta)

/-! ## Transport of a loop along a decoding with a section -/

section Conjugate

variable {X Y : Ty Empty} {d : Region signature.Instr}

/-- The arrow of `postRegion`, in default Paper. -/
theorem post_arrow (hx : ValueBranches [X] d [Y]) :
    ofRegion (postRegion_typed (B := Bit) hx) =
      (sumIso (Φ := signature.Instr) Bit X).hom ≫ coprod.map (𝟙 _) (ofRegion hx) ≫
        (sumIso (Φ := signature.Instr) Bit Y).inv := by
  have inlB : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit Y] :=
    .br rfl (.inl (.var rfl))
  have inrB : ValueBranches [Y] (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit Y] :=
    .br rfl (.inr (.var rfl))
  have l : ofRegion inlB = coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit Y).inv :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))
  have r : ofRegion inrB = coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit Y).inv :=
    (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Y)).trans (Category.id_comp _))
  have m := (ofRegion_comp hx inrB (seqRegion_typed hx inrB)).symm
  have c := coprod_desc_ofRegion inlB (seqRegion_typed hx inrB)
  rw [l, m, r] at c
  refine c.symm.trans ?_
  congr 1
  apply coprod.hom_ext <;> simp

theorem q_iter {A : Ty Empty} {p p' : Region signature.Instr} (hp : ValueBranches [A] p [Silmaril.coprod Bit A])
    (hp' : ValueBranches [A] p' [Silmaril.coprod Bit A]) (e : QLit hp = QLit hp') :
    QLit (loopRegion_typed hp) = QLit (loopRegion_typed hp') := by
  have a : ∀ {k : Region signature.Instr} (hk : ValueBranches [A] k [Silmaril.coprod Bit A]),
      QLit (loopRegion_typed hk) = iterateSum N (QLit hk) := fun hk =>
    ((iterateSum_map N (ofRegion hk)).trans
      (congrArg (π).map (Paper.TypeCategory.iterateSum_ofRegion hk))).symm
  rw [a hp, a hp', e]

end Conjugate

/-- A loop on `S` whose body, conjugated by an encoding with a section,
is the dispatcher step of a router table, factors through the packed loop
of that table. The roll law of iteration, in default Paper, and the
section, in the quotient. -/
theorem conjugate_factors {S : Ty Empty} {K : Nat} {enc dec body : Region signature.Instr}
    (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hb : ValueBranches [S] body [Silmaril.coprod Bit S]) (ret : Retracts S enc dec) (t : Router K)
    (hstep : Eqv false [States K] (seqRegion dec (seqRegion body (postRegion enc))) (dispatch K t.rows)
      [Silmaril.coprod Bit (States K)]) : Factors dec (loopRegion S body) t := by
  have conj : ValueBranches [States K] (seqRegion dec (seqRegion body (postRegion enc)))
      [Silmaril.coprod Bit (States K)] := seqRegion_typed hd (seqRegion_typed hb (postRegion_typed he))
  have body' : ValueBranches [S] (seqRegion body (postRegion (seqRegion enc dec))) [Silmaril.coprod Bit S] :=
    seqRegion_typed hb (postRegion_typed (seqRegion_typed he hd))
  -- default Paper: the roll law
  have a₁ := (ofRegion_comp hd (seqRegion_typed hb (postRegion_typed (B := Bit) he)) conj).symm
  have a₂ := (ofRegion_comp hb (postRegion_typed (B := Bit) he)
    (seqRegion_typed hb (postRegion_typed (B := Bit) he))).symm
  have c₁ : ofRegion conj ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      ofRegion hd ≫ ((ofRegion hb ≫ (sumIso (Φ := signature.Instr) Bit S).hom) ≫
        coprod.map (𝟙 _) (ofRegion he)) := by
    rw [a₁, a₂, post_arrow he]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have b₁ := (ofRegion_comp hb (postRegion_typed (B := Bit) (seqRegion_typed he hd)) body').symm
  have b₂ := (ofRegion_comp he hd (seqRegion_typed he hd)).symm
  have c₂ : ofRegion body' ≫ (sumIso (Φ := signature.Instr) Bit S).hom =
      ((ofRegion hb ≫ (sumIso (Φ := signature.Instr) Bit S).hom) ≫ coprod.map (𝟙 _) (ofRegion he)) ≫
        coprod.map (𝟙 _) (ofRegion hd) := by
    rw [b₁, post_arrow (seqRegion_typed he hd), b₂]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, coprod.map_map]
  have roll := iterate_roll (ofRegion hd)
    ((ofRegion hb ≫ (sumIso (Φ := signature.Instr) Bit S).hom) ≫ coprod.map (𝟙 _) (ofRegion he))
  rw [← c₁, ← c₂, iterate_exact conj, iterate_exact body'] at roll
  -- the quotient
  have one : QLit (seqRegion_typed he hd) = QLit (idRegion_typed S) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed he hd) (idRegion_typed S)).2 ret
  have post_id : ofRegion (postRegion_typed (B := Bit) (idRegion_typed S)) = 𝟙 _ := by
    rw [post_arrow (idRegion_typed S), ofRegion_id]
    simp
  have inlS : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit S] :=
    .br rfl (.inl (.var rfl))
  have inrS : ValueBranches [S] (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit S] :=
    .br rfl (.inr (.var rfl))
  have post_one : QLit (postRegion_typed (B := Bit) (seqRegion_typed he hd)) = 𝟙 _ :=
    (q_case_congr inlS (seqRegion_typed (seqRegion_typed he hd) inrS) inlS
      (seqRegion_typed (idRegion_typed S) inrS) rfl
      ((q_comp (seqRegion_typed he hd) inrS).trans
        ((congrArg (· ≫ QLit inrS) one).trans (q_comp (idRegion_typed S) inrS).symm))).trans
      ((congrArg (π).map post_id).trans ((π).map_id _))
  have same : QLit body' = QLit hb :=
    (q_comp hb (postRegion_typed (B := Bit) (seqRegion_typed he hd))).trans
      ((congrArg (QLit hb ≫ ·) post_one).trans (Category.comp_id _))
  have step : QLit conj = QLit (dispatch_typed K t.rows_typed) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N conj (dispatch_typed K t.rows_typed)).2 hstep
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed hd (loopRegion_typed hb)) t.loop_typed).1
  exact (q_comp hd (loopRegion_typed hb)).trans
    ((congrArg (QLit hd ≫ ·) (q_iter hb body' same.symm)).trans
      ((((π).map_comp _ _).symm.trans (congrArg (π).map roll.symm)).trans
        (q_iter conj (dispatch_typed K t.rows_typed) step)))

/-! ## A loop written on pairs -/

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- If the conjugated bodies are the dispatcher steps, the two loops on
pairs are equal exactly when they are valid in every supported model. -/
theorem pair_complete_of (l l' : Bool) (h : Task.pairStep l) (h' : Task.pairStep l') :
    Eqv false [Pair] (loopRegion Pair (pairBody l)) (loopRegion Pair (pairBody l')) [Bit] ↔
      Valid (loopRegion_typed (pairBody_typed l)).hasType (loopRegion_typed (pairBody_typed l')).hasType :=
  factored_complete pairEnc_typed pairDec_typed (loopRegion_typed (pairBody_typed l))
    (loopRegion_typed (pairBody_typed l')) enc_dec (pairRouter l) (pairRouter l')
    (conjugate_factors pairEnc_typed pairDec_typed (pairBody_typed l) enc_dec (pairRouter l) h)
    (conjugate_factors pairEnc_typed pairDec_typed (pairBody_typed l') enc_dec (pairRouter l') h')

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
