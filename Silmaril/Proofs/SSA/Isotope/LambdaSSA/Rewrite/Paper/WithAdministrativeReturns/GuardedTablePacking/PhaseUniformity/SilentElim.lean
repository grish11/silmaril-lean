module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EnvTables
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Defs

/-! # Eliminating ranked silent paths, in default Paper -/

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
open Silmaril.DeBruijn (lift)
open Paper.TypeCategory (iterate_fixpoint iterate_codiagonal)

/-! ## An inner loop over selected states -/

section Inner

variable {X Y : Paper.TypeCategory (τ := Ty Empty) signature.Instr} (f : X ⟶ Y ⨿ X) (d : X ⟶ X ⨿ X)

/-- One step of `f`; a state that `d` sends left repeats in the inner
loop, a state it sends right leaves it. -/
noncomputable def innerStep : X ⟶ (Y ⨿ X) ⨿ X :=
  f ≫ coprod.desc (coprod.inl ≫ coprod.inl) (d ≫ coprod.desc coprod.inr (coprod.inr ≫ coprod.inl))

/-- Run `f` until it returns or reaches a state that `d` sends right. -/
noncomputable def settle : X ⟶ Y ⨿ X := Paper.TypeCategory.iterate (innerStep f d)

/-- What follows a step inside `settle`. -/
noncomputable def settlePost : Y ⨿ X ⟶ Y ⨿ X :=
  coprod.desc coprod.inl (d ≫ coprod.desc (settle f d) coprod.inr)

theorem settle_fix : settle f d = f ≫ settlePost f d := by
  have fix := iterate_fixpoint (innerStep f d)
  refine fix.trans ?_
  have inner : coprod.desc coprod.inr (coprod.inr ≫ coprod.inl) ≫
      coprod.desc (𝟙 (Y ⨿ X)) (Paper.TypeCategory.iterate (innerStep f d)) =
      coprod.desc (settle f d) (coprod.inr : X ⟶ Y ⨿ X) := by
    apply coprod.hom_ext <;> simp [settle]
  have post : coprod.desc (coprod.inl ≫ coprod.inl)
      (d ≫ coprod.desc coprod.inr (coprod.inr ≫ coprod.inl)) ≫
      coprod.desc (𝟙 (Y ⨿ X)) (Paper.TypeCategory.iterate (innerStep f d)) = settlePost f d := by
    unfold settlePost
    apply coprod.hom_ext
    · simp
    · rw [coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc, inner]
  exact (Category.assoc _ _ _).trans (congrArg (f ≫ ·) post)

theorem settle_iterate (hd : d ≫ coprod.desc (𝟙 X) (𝟙 X) = 𝟙 X) :
    Paper.TypeCategory.iterate (settle f d) = Paper.TypeCategory.iterate f := by
  have co := iterate_codiagonal (innerStep f d)
  have flat : innerStep f d ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr = f := by
    unfold innerStep
    rw [Category.assoc]
    have inner : (d ≫ coprod.desc coprod.inr (coprod.inr ≫ coprod.inl)) ≫
        coprod.desc (𝟙 (Y ⨿ X)) coprod.inr = (coprod.inr : X ⟶ Y ⨿ X) := by
      have e : coprod.desc coprod.inr (coprod.inr ≫ coprod.inl) ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr =
          coprod.desc (𝟙 X) (𝟙 X) ≫ (coprod.inr : X ⟶ Y ⨿ X) := by
        apply coprod.hom_ext <;> simp
      rw [Category.assoc, e, ← Category.assoc, hd, Category.id_comp]
    have e : coprod.desc (coprod.inl ≫ coprod.inl)
        (d ≫ coprod.desc coprod.inr (coprod.inr ≫ coprod.inl)) ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr =
        𝟙 (Y ⨿ X) := by
      apply coprod.hom_ext
      · simp
      · rw [coprod.inr_desc_assoc, inner, Category.comp_id]
    rw [e, Category.comp_id]
  rw [flat] at co
  exact co

/-- Continuing the loop after `settlePost` is continuing the loop. -/
theorem settlePost_loop (hd : d ≫ coprod.desc (𝟙 X) (𝟙 X) = 𝟙 X) :
    settlePost f d ≫ coprod.desc (𝟙 Y) (Paper.TypeCategory.iterate f) =
      coprod.desc (𝟙 Y) (Paper.TypeCategory.iterate f) := by
  have fix : settle f d ≫ coprod.desc (𝟙 Y) (Paper.TypeCategory.iterate f) = Paper.TypeCategory.iterate f := by
    have e := iterate_fixpoint (settle f d)
    rw [settle_iterate f d hd] at e
    exact e.symm
  unfold settlePost
  apply coprod.hom_ext
  · simp
  · rw [coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
    have e : coprod.desc (settle f d) coprod.inr ≫ coprod.desc (𝟙 Y) (Paper.TypeCategory.iterate f) =
        coprod.desc (𝟙 X) (𝟙 X) ≫ Paper.TypeCategory.iterate f := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, fix]
        simp
      · simp
    rw [e, ← Category.assoc, hd, Category.id_comp]

end Inner

/-! ## Deciding silent states -/

section Decide

variable {M : Nat}

def sideTm (b : Bool) (t : Tm signature.Instr) : Tm signature.Instr :=
  match b with
  | true => .inl t
  | false => .inr t

theorem sideTm_typed {X A : Ty Empty} {t : Tm signature.Instr} (b : Bool) (ht : Tm.BranchValue [X] t A) :
    Tm.BranchValue [X] (sideTm b t) (Silmaril.coprod A A) := by
  cases b
  · exact .inr ht
  · exact .inl ht

def sideRows (M : Nat) (s : Fin (M + 1) → Bool) (y : Fin (M + 1)) : Region signature.Instr :=
  .br 0 (sideTm (s y) (injTm M y (.var 0)))

theorem sideRows_typed (s : Fin (M + 1) → Bool) (y : Fin (M + 1)) :
    ValueBranches [State] (sideRows M s y) [Silmaril.coprod (States M) (States M)] :=
  .br rfl (sideTm_typed (s y) (injTm_typed (.var rfl) M y))

/-- Send a state left when `s` holds and right otherwise. -/
noncomputable def sideArr (s : Fin (M + 1) → Bool) :
    ofType (Φ := signature.Instr) (States M) ⟶ ofType (States M) ⨿ ofType (States M) :=
  ofRegion (dispatch_typed M (sideRows_typed s)) ≫ (sumIso (Φ := signature.Instr) (States M) (States M)).hom

theorem inj_side (s : Fin (M + 1) → Bool) (y : Fin (M + 1)) :
    injArr M y ≫ sideArr s = injArr M y ≫ (match s y with | true => coprod.inl | false => coprod.inr) := by
  unfold sideArr
  rw [← Category.assoc, inj_dispatch M (sideRows_typed s) y]
  have e : ∀ b : Bool, ofRegion (r := .br 0 (sideTm b (injTm M y (.var 0))))
      (.br (L := [Silmaril.coprod (States M) (States M)]) rfl (sideTm_typed b (injTm_typed (.var rfl) M y))) ≫
        (sumIso (Φ := signature.Instr) (States M) (States M)).hom =
      injArr M y ≫ (match b with | true => coprod.inl | false => coprod.inr) := fun b => by
    cases b
    · rw [show ofRegion (r := .br 0 (sideTm false (injTm M y (.var 0))))
        (.br (L := [Silmaril.coprod (States M) (States M)]) rfl
          (sideTm_typed false (injTm_typed (.var rfl) M y))) = _ from br_inr (injTm_typed (.var rfl) M y)]
      simp [injArr]
    · rw [show ofRegion (r := .br 0 (sideTm true (injTm M y (.var 0))))
        (.br (L := [Silmaril.coprod (States M) (States M)]) rfl
          (sideTm_typed true (injTm_typed (.var rfl) M y))) = _ from br_inl (injTm_typed (.var rfl) M y)]
      simp [injArr]
  exact e (s y)

theorem side_codiag (s : Fin (M + 1) → Bool) :
    sideArr s ≫ coprod.desc (𝟙 _) (𝟙 _) = 𝟙 (ofType (Φ := signature.Instr) (States M)) := by
  apply inj_ext M
  intro y
  rw [← Category.assoc, inj_side, Category.comp_id]
  cases s y <;> simp

end Decide

/-! ## Resolution of actions -/

section Resolve

variable {M : Nat} (sil : Fin (M + 1) → Option (Act M))

theorem resolveN_ret (n : Nat) (b : Bool) : resolveN sil n (.ret b) = .ret b := by
  cases n <;> rfl

theorem resolveN_none (n : Nat) {y : Fin (M + 1)} (q : Bool) (h : sil y = none) :
    resolveN sil n (.go y q) = .go y q := by
  cases n with
  | zero => rfl
  | succ n =>
    show (match sil y with | some A => resolveN sil n A | none => Act.go y q) = _
    rw [h]

theorem resolveN_some (n : Nat) {y : Fin (M + 1)} (q : Bool) {A : Act M} (h : sil y = some A) :
    resolveN sil (n + 1) (.go y q) = resolveN sil n A := by
  show (match sil y with | some A => resolveN sil n A | none => Act.go y q) = _
  rw [h]

/-- With a ranking, the fuel resolves every action. -/
theorem ranked_settled {rank : Fin (M + 1) → Nat}
    (down : ∀ y A, sil y = some A → ∀ z q, A = .go z q → ∀ B, sil z = some B → rank z < rank y) :
    ∀ (n : Nat) (a : Act M), (∀ y q, a = .go y q → ∀ A, sil y = some A → rank y < n) →
      (resolveN sil n a).Settled sil
  | _, .ret b, _ => by
    rw [resolveN_ret]
    exact True.intro
  | 0, .go y q, h => by
    cases hy : sil y with
    | none => exact hy
    | some A => exact absurd (h y q rfl A hy) (Nat.not_lt_zero _)
  | n + 1, .go y q, h => by
    cases hy : sil y with
    | none =>
      rw [resolveN_none sil (n + 1) q hy]
      exact hy
    | some A =>
      rw [resolveN_some sil n q hy]
      exact ranked_settled down n A fun z q' e B hz =>
        Nat.lt_of_lt_of_le (down y A hy z q' e B hz) (Nat.le_of_lt_succ (h y q rfl A hy))

theorem resolve_carries (c : Fin (M + 1) → Bool) (hcar : ∀ y A, sil y = some A → A.Carries c) :
    ∀ (n : Nat) (a : Act M), a.Carries c → (resolveN sil n a).Carries c
  | _, .ret b, _ => by
    rw [resolveN_ret]
    exact True.intro
  | 0, .go y q, h => h
  | n + 1, .go y q, h => by
    cases hy : sil y with
    | none =>
      rw [resolveN_none sil (n + 1) q hy]
      exact h
    | some A =>
      rw [resolveN_some sil n q hy]
      exact resolve_carries c hcar n A (hcar y A hy)

end Resolve

/-! ## Eliminating silent states from a router table -/

section Elim

variable {M : Nat} (t : Router M) (c : Fin (M + 1) → Bool) (sil : Fin (M + 1) → Option (Act M))

/-- The dispatcher step of a table, as a step of iteration. -/
noncomputable def stepArr : ofType (Φ := signature.Instr) (States M) ⟶ ofType Bit ⨿ ofType (States M) :=
  ofRegion (dispatch_typed M t.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom

theorem stepArr_eq : stepArr t =
    ofRegion (dispatch_typed M t.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  rfl

theorem loop_iterate :
    ofRegion (dispatchLoop_typed t.rows_typed) = Paper.TypeCategory.iterate (stepArr t) :=
  dispatchLoop_arrow t.rows_typed

/-- What follows a step: resolve the silent states. -/
noncomputable def silPost :
    ofType (Φ := signature.Instr) Bit ⨿ ofType (States M) ⟶ ofType Bit ⨿ ofType (States M) :=
  settlePost (stepArr t) (sideArr fun y => (sil y).isSome)

theorem act_ret_arrow (b : Bool) :
    ofRegion (act_typed M (.ret b)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom =
      ofRegion (bit_typed b) ≫ coprod.inl := by
  have e : ofRegion (act_typed M (.ret b)) =
      ofRegion (bit_typed b) ≫ (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv) :=
    br_inl (bitTm_typed b)
  rw [e]
  simp

theorem act_go_arrow (y : Fin (M + 1)) (q : Bool) :
    ofRegion (act_typed M (.go y q)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom =
      (ofRegion (const_typed q) ≫ injArr M y) ≫ coprod.inr := by
  have e : ofRegion (act_typed M (.go y q)) =
      (ofRegion (const_typed q) ≫ injArr M y) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv) :=
    (br_inr (injTm_typed (.inl (bitTm_typed q)) M y)).trans
      (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv))
        (injOf_eq (.inl (bitTm_typed q)) M y))
  rw [e]
  simp

theorem post_inr : (coprod.inr : ofType (Φ := signature.Instr) (States M) ⟶ _) ≫ silPost t sil =
    sideArr (fun y => (sil y).isSome) ≫
      coprod.desc (settle (stepArr t) (sideArr fun y => (sil y).isSome)) coprod.inr := by
  unfold silPost settlePost
  rw [coprod.inr_desc]

theorem post_inl : (coprod.inl : ofType (Φ := signature.Instr) Bit ⟶ _) ≫ silPost t sil = coprod.inl := by
  unfold silPost settlePost
  rw [coprod.inl_desc]

theorem go_post (y : Fin (M + 1)) (q : Bool) :
    (ofRegion (act_typed M (.go y q)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      ofRegion (const_typed q) ≫ (injArr M y ≫ sideArr fun y => (sil y).isSome) ≫
        coprod.desc (settle (stepArr t) (sideArr fun y => (sil y).isSome)) coprod.inr := by
  rw [act_go_arrow]
  simp only [Category.assoc]
  rw [post_inr]

theorem side_none {y : Fin (M + 1)} (hy : sil y = none) :
    (injArr M y ≫ sideArr fun y => (sil y).isSome) = injArr M y ≫ coprod.inr := by
  have s := inj_side (fun y => (sil y).isSome) y
  rw [hy] at s
  exact s

theorem side_some {y : Fin (M + 1)} {A : Act M} (hy : sil y = some A) :
    (injArr M y ≫ sideArr fun y => (sil y).isSome) = injArr M y ≫ coprod.inl := by
  have s := inj_side (fun y => (sil y).isSome) y
  rw [hy] at s
  exact s

/-- A repeat to a state that sends a request is not changed. -/
theorem stay_post {y : Fin (M + 1)} (q : Bool) (hy : sil y = none) :
    (ofRegion (act_typed M (.go y q)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      ofRegion (act_typed M (.go y q)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  rw [go_post, side_none sil hy, act_go_arrow]
  simp

theorem ret_post (b : Bool) :
    (ofRegion (act_typed M (.ret b)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      ofRegion (act_typed M (.ret b)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  rw [act_ret_arrow, Category.assoc, post_inl]

variable (hsil : ∀ y A, sil y = some A →
    ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) = ofRegion (act_typed M A))
  (hcar : ∀ y A, sil y = some A → A.Carries c)

include hsil in
/-- A repeat to a silent state takes that state's action. -/
theorem hop_post {y : Fin (M + 1)} {A : Act M} (hy : sil y = some A) :
    (ofRegion (act_typed M (.go y (c y))) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      (ofRegion (act_typed M A) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil := by
  have enter : ofRegion (const_typed (c y)) ≫ injArr M y ≫ stepArr t =
      ofRegion (act_typed M A) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
    unfold stepArr
    rw [← Category.assoc (injArr M y), inj_dispatch M t.rows_typed y, ← Category.assoc,
      ofRegion_comp (const_typed (c y)) (t.rows_typed y)
        (seqValueBranches (const_typed (c y)) (t.rows_typed y)), hsil y A hy]
  rw [go_post, side_some sil hy]
  simp only [Category.assoc, coprod.inl_desc]
  rw [settle_fix]
  exact ((Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ settlePost (stepArr t) (sideArr fun y => (sil y).isSome))
      ((Category.assoc _ _ _).trans enter)))).trans (Category.assoc _ _ _)

include hsil hcar in
/-- An action followed by the resolution of silent states is the resolved
action. Induction on the fuel. In default Paper. -/
theorem act_settle : ∀ (n : Nat) (a : Act M), a.Carries c → (resolveN sil n a).Settled sil →
    (ofRegion (act_typed M a) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      ofRegion (act_typed M (resolveN sil n a)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom
  | n, .ret b, _, _ => by
    rw [resolveN_ret]
    exact ret_post t sil b
  | 0, .go y q, _, hs => stay_post t sil q hs
  | n + 1, .go y q, hc, hs => by
    cases hy : sil y with
    | none =>
      rw [resolveN_none sil (n + 1) q hy]
      exact stay_post t sil q hy
    | some A =>
      rw [resolveN_some sil n q hy] at hs ⊢
      have cy : c y = q := hc
      subst cy
      exact (hop_post t c sil hsil hy).trans (act_settle n A (hcar y A hy) hs)

end Elim

/-! ## The resolved table -/

section Table

variable {M : Nat} (t : Router M) (c : Fin (M + 1) → Bool) (sil : Fin (M + 1) → Option (Act M)) (n : Nat)
  (hsil : ∀ y A, sil y = some A →
    ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) = ofRegion (act_typed M A))
  (hcar : ∀ y A, sil y = some A → A.Carries c)
  (hact : ∀ x a b, (t.act x a b).Carries c)
  (hset : ∀ x a b, (resolveN sil n (t.act x a b)).Settled sil)

include hsil hcar hact hset in
theorem step_settle : stepArr t ≫ silPost t sil = stepArr (t.resolved sil n) := by
  apply inj_ext M
  intro x
  have row : (ofRegion (t.rows_typed x) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫ silPost t sil =
      ofRegion ((t.resolved sil n).rows_typed x) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom :=
    gen_post (silPost t sil) (post_inl t sil) (t.prog x) (fun a b => act_typed M (t.act x a b))
      (fun a b => act_typed M (resolveN sil n (t.act x a b)))
      (fun a b => act_settle t c sil hsil hcar n (t.act x a b) (hact x a b) (hset x a b))
  unfold stepArr
  rw [← Category.assoc, ← Category.assoc, inj_dispatch M t.rows_typed x, ← Category.assoc,
    inj_dispatch M (t.resolved sil n).rows_typed x]
  exact row

include hsil hcar hact hset in
/-- The table and its resolved table have the same loop. In default Paper. -/
theorem silent_loop :
    ofRegion (dispatchLoop_typed (t.resolved sil n).rows_typed) = ofRegion (dispatchLoop_typed t.rows_typed) := by
  rw [loop_iterate, loop_iterate, ← step_settle t c sil n hsil hcar hact hset]
  have fix := settle_fix (stepArr t) (sideArr fun y => (sil y).isSome)
  have it := settle_iterate (stepArr t) (sideArr fun y => (sil y).isSome) (side_codiag _)
  rw [fix] at it
  exact it

include hsil hcar hact hset in
/-- So they have the same entered loops at every state. -/
theorem silent_entered (x : Fin (M + 1)) :
    ofRegion ((t.resolved sil n).entered_typed x) = ofRegion (t.entered_typed x) := by
  show ofRegion (dispatchEntered_typed (t.resolved sil n).rows_typed x) =
    ofRegion (dispatchEntered_typed t.rows_typed x)
  rw [dispatchEntered_arrow (t.resolved sil n).rows_typed x, dispatchEntered_arrow t.rows_typed x,
    silent_loop t c sil n hsil hcar hact hset]

/-- The loop of a table continued after an action. -/
noncomputable def Act.arrow (t : Router M) : Act M → (ofType (Φ := signature.Instr) U ⟶ ofType Bit)
  | .ret b => ofRegion (bit_typed b)
  | .go y q => ofRegion (const_typed q) ≫ ofRegion (t.entered_typed y)

theorem arrow_ret (b : Bool) : Act.arrow t (.ret b) = ofRegion (bit_typed b) := by
  rfl

theorem arrow_go (y : Fin (M + 1)) (q : Bool) :
    Act.arrow t (.go y q) = ofRegion (const_typed q) ≫ ofRegion (t.entered_typed y) := by
  rfl

theorem act_loop (a : Act M) :
    (ofRegion (act_typed M a) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.desc (𝟙 _) (ofRegion (dispatchLoop_typed t.rows_typed)) = Act.arrow t a := by
  cases a with
  | ret b =>
    rw [act_ret_arrow]
    simp [Act.arrow]
  | go y q =>
    rw [act_go_arrow]
    show _ = ofRegion (const_typed q) ≫ ofRegion (dispatchEntered_typed t.rows_typed y)
    rw [dispatchEntered_arrow t.rows_typed y]
    simp

include hsil hcar hact hset in
/-- The elimination of ranked silent paths at an entry: the table entered
with a constant is the resolved table continued after the resolved entry.
In default Paper. -/
theorem silent_entry (x : Fin (M + 1)) (hx : (resolveN sil n (.go x (c x))).Settled sil) :
    ofRegion (const_typed (c x)) ≫ ofRegion (t.entered_typed x) =
      Act.arrow (t.resolved sil n) (resolveN sil n (.go x (c x))) := by
  have post := settlePost_loop (stepArr t) (sideArr fun y => (sil y).isSome) (side_codiag _)
  have loop := silent_loop t c sil n hsil hcar hact hset
  have start := act_loop t (.go x (c x))
  have settled := act_settle t c sil hsil hcar n (.go x (c x)) rfl hx
  rw [← act_loop (t.resolved sil n), loop, ← settled, Category.assoc, loop_iterate]
  show _ = _ ≫ settlePost (stepArr t) (sideArr fun y => (sil y).isSome) ≫ _
  rw [post, ← loop_iterate]
  exact start.symm

end Table

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
