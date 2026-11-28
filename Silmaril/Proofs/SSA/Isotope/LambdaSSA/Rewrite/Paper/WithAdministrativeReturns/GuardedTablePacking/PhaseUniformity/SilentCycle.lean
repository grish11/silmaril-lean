module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentTables
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Defs

/-! # Silent cycles are the canonical silent self-loop -/

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
open Paper.TypeCategory (iterate_roll)

/-! ## Arrows out of a state -/

theorem const_reset_to (q q' : Bool) :
    ofRegion (const_typed q) ≫ ofRegion (reset_typed q') = ofRegion (const_typed q') := by
  have a := ofRegion_comp (const_typed q) (reset_typed q') (seqValueBranches (const_typed q) (reset_typed q'))
  have b := const_case q (const_typed q') (const_typed q') emptyState_typed
  cases q <;> exact a.trans b

/-- Arrows out of a state are equal when they agree on the two constants. -/
theorem state_hom_ext {Z : Paper.TypeCategory (τ := Ty Empty) signature.Instr}
    {f g : ofType (Φ := signature.Instr) State ⟶ Z}
    (h : ∀ b, ofRegion (const_typed b) ≫ f = ofRegion (const_typed b) ≫ g) : f = g := by
  have bits : ofRegion bitState_typed ≫ f = ofRegion bitState_typed ≫ g := by
    rw [← cancel_epi (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv]
    apply coprod.hom_ext
    · have e := h false
      rw [const_arrow, bitTm_false_arrow] at e
      simpa [Category.assoc] using e
    · have e := h true
      rw [const_arrow, bitTm_true_arrow] at e
      simpa [Category.assoc] using e
  rw [← cancel_epi (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv]
  apply coprod.hom_ext
  · rw [bitState_arrow] at bits
    simpa [Category.assoc] using bits
  · exact Paper.TypeCategory.emptyIsInitial.hom_ext _ _

/-- A reset followed by an arrow is determined by the arrow on the
constant it resets to. -/
theorem reset_hom_ext {Z : Paper.TypeCategory (τ := Ty Empty) signature.Instr} (q q' : Bool)
    {f g : ofType (Φ := signature.Instr) State ⟶ Z}
    (h : ofRegion (const_typed q) ≫ f = ofRegion (const_typed q') ≫ g) :
    ofRegion (reset_typed q) ≫ f = ofRegion (reset_typed q') ≫ g :=
  state_hom_ext fun b => by
    rw [← Category.assoc, ← Category.assoc, const_reset_to, const_reset_to, h]

section Resets

variable {M : Nat} (c c' : Fin (M + 1) → Bool)

/-- A reset after a reset is the later reset. -/
theorem reset_reset : resetArr c' ≫ resetArr c = resetArr c := by
  apply inj_ext M
  intro y
  rw [← Category.assoc, inj_reset, Category.assoc, inj_reset, ← Category.assoc]
  refine congrArg (· ≫ injArr M y) ?_
  exact state_hom_ext fun b => by
    rw [← Category.assoc, const_reset_to, const_reset_to, const_reset_to]

variable {rows : Fin (M + 1) → Region signature.Instr}
  (h : ∀ x, ValueBranches [State] (rows x) [Silmaril.coprod Bit (States M)])

theorem matched_step (m : Matched c h) :
    (ofRegion (dispatch_typed M h) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.map (𝟙 _) (resetArr c) =
      ofRegion (dispatch_typed M h) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  apply inj_ext M
  intro x
  simp only [← Category.assoc]
  rw [inj_dispatch M h x]
  exact m x

end Resets

/-! ## Dulling the Bits carried into a closed silent set -/

section Dull

variable {M : Nat}

/-- The Bit carried into a state: `false` at a state of `cyc`. -/
def dullBit (cyc : Fin (M + 1) → Bool) (c : Fin (M + 1) → Bool) (y : Fin (M + 1)) : Bool :=
  match cyc y with
  | true => false
  | false => c y

theorem dullBit_false {cyc c : Fin (M + 1) → Bool} {y : Fin (M + 1)} (h : cyc y = false) :
    dullBit cyc c y = c y := by
  unfold dullBit
  rw [h]

theorem dullBit_true {cyc c : Fin (M + 1) → Bool} {y : Fin (M + 1)} (h : cyc y = true) :
    dullBit cyc c y = false := by
  unfold dullBit
  rw [h]

def dullProg (b : Bool) (p : Program) : Program :=
  match b with
  | true => .ret 0 0
  | false => p

def dullRow (cyc : Fin (M + 1) → Bool) (b : Bool) (z : Fin (M + 1)) (a : Bool → Bool → Act M) :
    Bool → Bool → Act M :=
  match b with
  | true => fun _ _ => .go z false
  | false => fun x y => dullAct cyc (a x y)

/-- The table with each state of `cyc` replaced by a constant row that
repeats to its successor with `false`, and every Bit carried into `cyc`
replaced by `false`. -/
def dulled (t : Router M) (cyc : Fin (M + 1) → Bool) (nxt : Fin (M + 1) → Fin (M + 1)) : Router M :=
  ⟨fun y => dullProg (cyc y) (t.prog y), fun y => dullRow cyc (cyc y) (nxt y) (t.act y)⟩

variable (t : Router M) (c : Fin (M + 1) → Bool) (cyc : Fin (M + 1) → Bool) (nxt : Fin (M + 1) → Fin (M + 1))

theorem dullAct_carries (a : Act M) (h : a.Carries c) : (dullAct cyc a).Carries (dullBit cyc c) := by
  cases a with
  | ret b => exact True.intro
  | go y q =>
    have cy : c y = q := h
    subst cy
    rfl

/-- Resetting to the dulled Bits after an action dulls the action. -/
theorem dull_leaf (a : Act M) (h : a.Carries c) :
    (ofRegion (act_typed M a) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
      ofRegion (act_typed M (dullAct cyc a)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  cases a with
  | ret b =>
    show _ = ofRegion (act_typed M (.ret b)) ≫ _
    rw [act_ret_arrow]
    simp
  | go y q =>
    have cy : c y = q := h
    subst cy
    show _ = ofRegion (act_typed M (.go y (dullBit cyc c y))) ≫ _
    rw [act_go_arrow, act_go_arrow]
    simp only [Category.assoc, coprod.inr_map]
    rw [← Category.assoc (injArr M y), inj_reset, Category.assoc, ← Category.assoc (ofRegion (const_typed (c y))),
      const_reset_to]

variable (hact : ∀ x a b, (t.act x a b).Carries c)
  (hcyc : ∀ y, cyc y = true →
    ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) =
      ofRegion (act_typed M (.go (nxt y) (c (nxt y)))) ∧ cyc (nxt y) = true)

include hact hcyc in
theorem dulled_carries (x : Fin (M + 1)) (a b : Bool) :
    ((dulled t cyc nxt).act x a b).Carries (dullBit cyc c) := by
  show (dullRow cyc (cyc x) (nxt x) (t.act x) a b).Carries (dullBit cyc c)
  cases hx : cyc x with
  | true =>
    show dullBit cyc c (nxt x) = false
    unfold dullBit
    rw [(hcyc x hx).2]
  | false => exact dullAct_carries c cyc _ (hact x a b)

include hact hcyc in
/-- A row of the table entered with its Bit, with the dulled reset after
it, is the dulled row entered with its dulled Bit. -/
theorem dull_row (y : Fin (M + 1)) :
    ofRegion (const_typed (c y)) ≫
        (ofRegion (t.rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
          coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
      ofRegion (const_typed (dullBit cyc c y)) ≫
        ofRegion ((dulled t cyc nxt).rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  have general : ∀ b : Bool, cyc y = b →
      ofRegion (const_typed (c y)) ≫
          (ofRegion (t.rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
            coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
        ofRegion (const_typed (match b with | true => false | false => c y)) ≫
          ofRegion (routerRow_typed M (dullProg b (t.prog y)) (dullRow cyc b (nxt y) (t.act y))) ≫
            (sumIso (Φ := signature.Instr) Bit (States M)).hom := fun b hb => by
    cases b with
    | false =>
      refine congrArg (ofRegion (const_typed (c y)) ≫ ·) ?_
      exact gen_post (coprod.map (𝟙 _) (resetArr (dullBit cyc c))) (by simp) (t.prog y)
        (fun a b => act_typed M (t.act y a b)) (fun a b => act_typed M (dullAct cyc (t.act y a b)))
        (fun a b => dull_leaf c cyc (t.act y a b) (hact y a b))
    | true =>
      obtain ⟨row, next⟩ := hcyc y hb
      have lhs : ofRegion (const_typed (c y)) ≫ ofRegion (t.rows_typed y) =
          ofRegion (act_typed M (.go (nxt y) (c (nxt y)))) :=
        (ofRegion_comp (const_typed (c y)) (t.rows_typed y) _).trans row
      have leaf := dull_leaf c cyc (.go (nxt y) (c (nxt y))) rfl
      have dulled_leaf : dullAct cyc (.go (nxt y) (c (nxt y))) = .go (nxt y) false := by
        show Act.go (nxt y) (match cyc (nxt y) with | true => false | false => c (nxt y)) = _
        rw [next]
      rw [dulled_leaf] at leaf
      have rhs : ofRegion (const_typed false) ≫ ofRegion (routerRow_typed M (.ret 0 0) fun _ _ => .go (nxt y) false) =
          ofRegion (act_typed M (.go (nxt y) false)) :=
        (ofRegion_comp (const_typed false) (routerRow_typed M (.ret 0 0) fun _ _ => .go (nxt y) false) _).trans
          (pure_const M 0 (fun _ _ => .go (nxt y) false) false)
      calc
        _ = (ofRegion (act_typed M (.go (nxt y) (c (nxt y)))) ≫
              (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
              coprod.map (𝟙 _) (resetArr (dullBit cyc c)) := by
          rw [← lhs]
          simp only [Category.assoc]
        _ = ofRegion (act_typed M (.go (nxt y) false)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := leaf
        _ = _ := by
          rw [← rhs]
          simp only [Category.assoc]
  have e := general (cyc y) rfl
  exact e

end Dull

/-! ## The loop of the dulled table -/

section Loop

variable {M : Nat} (t : Router M) (c : Fin (M + 1) → Bool) (cyc : Fin (M + 1) → Bool)
  (nxt : Fin (M + 1) → Fin (M + 1)) (hact : ∀ x a b, (t.act x a b).Carries c)
  (hcyc : ∀ y, cyc y = true →
    ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) =
      ofRegion (act_typed M (.go (nxt y) (c (nxt y)))) ∧ cyc (nxt y) = true)

include hact hcyc in
/-- After their resets, the table and its dulled table have the same
loop. In default Paper. -/
theorem dull_loop :
    resetArr c ≫ ofRegion (dispatchLoop_typed t.rows_typed) =
      resetArr (dullBit cyc c) ≫ ofRegion (dispatchLoop_typed (dulled t cyc nxt).rows_typed) := by
  have m : Matched c t.rows_typed := router_matched c t hact
  have m' : Matched (dullBit cyc c) (dulled t cyc nxt).rows_typed :=
    router_matched (dullBit cyc c) (dulled t cyc nxt) (dulled_carries t c cyc nxt hact hcyc)
  have steps : resetArr c ≫ stepArr t ≫ coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
      resetArr (dullBit cyc c) ≫ stepArr (dulled t cyc nxt) := by
    apply inj_ext M
    intro y
    have inj_step : ∀ s : Router M, injArr M y ≫ stepArr s =
        ofRegion (s.rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := fun s => by
      rw [stepArr_eq, ← Category.assoc, inj_dispatch M s.rows_typed y]
    have lhs : injArr M y ≫ resetArr c ≫ stepArr t ≫ coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
        ofRegion (reset_typed (c y)) ≫
          (ofRegion (t.rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
            coprod.map (𝟙 _) (resetArr (dullBit cyc c)) := by
      rw [← Category.assoc, inj_reset, Category.assoc, ← Category.assoc (injArr M y), inj_step]
    have rhs : injArr M y ≫ resetArr (dullBit cyc c) ≫ stepArr (dulled t cyc nxt) =
        ofRegion (reset_typed (dullBit cyc c y)) ≫
          ofRegion ((dulled t cyc nxt).rows_typed y) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
      rw [← Category.assoc, inj_reset, Category.assoc, inj_step]
    rw [lhs, rhs]
    exact reset_hom_ext (c y) (dullBit cyc c y) (dull_row t c cyc nxt hact hcyc y)
  have left := iterate_roll (resetArr c) (stepArr t ≫ coprod.map (𝟙 _) (resetArr (dullBit cyc c)))
  have right := iterate_roll (resetArr (dullBit cyc c)) (stepArr (dulled t cyc nxt))
  have back : (stepArr t ≫ coprod.map (𝟙 _) (resetArr (dullBit cyc c))) ≫ coprod.map (𝟙 _) (resetArr c) =
      stepArr t := by
    rw [Category.assoc, Limits.coprod.map_map, Category.comp_id, reset_reset, stepArr_eq]
    exact matched_step c t.rows_typed m
  have keep : stepArr (dulled t cyc nxt) ≫ coprod.map (𝟙 _) (resetArr (dullBit cyc c)) =
      stepArr (dulled t cyc nxt) := by
    rw [stepArr_eq]
    exact matched_step (dullBit cyc c) (dulled t cyc nxt).rows_typed m'
  rw [back] at left
  rw [keep] at right
  rw [loop_iterate, loop_iterate, ← left, ← right, steps]

include hact hcyc in
/-- The table entered with the Bit of a state is its dulled table entered
with the dulled Bit. In default Paper. -/
theorem dull_entry (x : Fin (M + 1)) :
    ofRegion (const_typed (c x)) ≫ ofRegion (t.entered_typed x) =
      ofRegion (const_typed (dullBit cyc c x)) ≫ ofRegion ((dulled t cyc nxt).entered_typed x) := by
  have loop := dull_loop t c cyc nxt hact hcyc
  have l : ofRegion (const_typed (c x)) ≫ injArr M x ≫ resetArr c =
      ofRegion (const_typed (c x)) ≫ injArr M x := by
    rw [inj_reset, ← Category.assoc, const_reset_to]
  have r : ofRegion (const_typed (c x)) ≫ injArr M x ≫ resetArr (dullBit cyc c) =
      ofRegion (const_typed (dullBit cyc c x)) ≫ injArr M x := by
    rw [inj_reset, ← Category.assoc, const_reset_to]
  show _ ≫ ofRegion (dispatchEntered_typed t.rows_typed x) =
    _ ≫ ofRegion (dispatchEntered_typed (dulled t cyc nxt).rows_typed x)
  rw [dispatchEntered_arrow t.rows_typed x, dispatchEntered_arrow (dulled t cyc nxt).rows_typed x]
  calc
    _ = (ofRegion (const_typed (c x)) ≫ injArr M x ≫ resetArr c) ≫
          ofRegion (dispatchLoop_typed t.rows_typed) := by
      rw [l, Category.assoc]
    _ = (ofRegion (const_typed (c x)) ≫ injArr M x ≫ resetArr (dullBit cyc c)) ≫
          ofRegion (dispatchLoop_typed (dulled t cyc nxt).rows_typed) := by
      simp only [Category.assoc]
      rw [loop]
    _ = _ := by
      rw [r, Category.assoc]

include hact hcyc in
/-- A state of a closed silent set, entered with its Bit, is the
canonical silent self-loop. The dulled table is bisimilar to it. -/
theorem cycle_spin (x : Fin (M + 1)) (hx : cyc x = true) :
    QLit (const_typed (c x)) ≫ QLit (t.entered_typed x) = QLit spinRegion_typed := by
  have bis : Eqv false [State] ((dulled t cyc nxt).entered x) (spinRouter.entered 0) [Bit] :=
    router_bisimulation_eqv (dulled t cyc nxt) spinRouter (fun y _ => cyc y = true)
      ⟨fun y _ hy => by
          show dullProg (cyc y) (t.prog y) = .ret 0 0
          rw [hy]
          rfl,
        fun y _ hy a b => by
          show Act.Rel (fun y _ => cyc y = true) (dullRow cyc (cyc y) (nxt y) (t.act y) a b) (.go 0 false)
          rw [hy]
          exact ⟨rfl, (hcyc y hy).2⟩⟩ x 0 hx
  have bit : dullBit cyc c x = false := by
    unfold dullBit
    rw [hx]
  have entry := dull_entry t c cyc nxt hact hcyc x
  rw [bit] at entry
  exact (((π).map_comp _ _).symm.trans (congrArg (π).map entry)).trans
    (((π).map_comp _ _).trans ((congrArg (QLit (const_typed false) ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 bis)).trans
        (q_const false (spinRouter.entered_typed 0)).symm))

include hact hcyc in
theorem cycle_spin_eqv (x : Fin (M + 1)) (hx : cyc x = true) :
    Eqv false [U] (constEntry (c x) (t.entered x)) spinRegion [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed (c x) (t.entered_typed x)) spinRegion_typed).1
    ((q_const (c x) (t.entered_typed x)).trans (cycle_spin t c cyc nxt hact hcyc x hx))

end Loop

/-! ## The dulled table as a table of labelled rows and silent rows -/

section Spun

variable {M : Nat} (t : Router M) (cyc : Fin (M + 1) → Bool) (nxt : Fin (M + 1) → Fin (M + 1))
  (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)

/-- At a labelled row, the dulled table is the table of labelled rows and
canonical silent rows. A bisimulation: the rows of `cyc` are related to
silent rows. -/
theorem dulled_spin
    (hlab : ∀ y l, label y = some l → cyc y = false ∧ t.prog y = (labelPoll l).program)
    (htgt : ∀ y l, label y = some l → ∀ a b z q, t.act y a b = .go z q →
      (∃ l', label z = some l') ∨ cyc z = true)
    (hnone : ∀ y, cyc y = true → label y = none ∧ cyc (nxt y) = true)
    (hact : ∀ y l, label y = some l → ∀ a b, act y a b = dullAct cyc (t.act y a b))
    (x : Fin (M + 1)) {l : Bool} (hx : label x = some l) :
    Eqv false [State] ((dulled t cyc nxt).entered x) ((Router.ofSpin label act).entered x) [Bit] :=
  router_bisimulation_eqv (dulled t cyc nxt) (Router.ofSpin label act)
    (fun j j' => (j = j' ∧ ∃ l, label j = some l) ∨ (cyc j = true ∧ cyc j' = true))
    ⟨fun j j' r => by
        show dullProg (cyc j) (t.prog j) = lsProg (label j')
        rcases r with ⟨e, l', hl⟩ | ⟨cj, cj'⟩
        · subst e
          rw [(hlab j l' hl).1, hl]
          exact (hlab j l' hl).2
        · rw [cj, (hnone j' cj').1]
          rfl,
      fun j j' r a b => by
        show Act.Rel _ (dullRow cyc (cyc j) (nxt j) (t.act j) a b) (lsAct (label j') j' (act j') a b)
        rcases r with ⟨e, l', hl⟩ | ⟨cj, cj'⟩
        · subst e
          rw [(hlab j l' hl).1, hl]
          show Act.Rel _ (dullAct cyc (t.act j a b)) (act j a b)
          rw [hact j l' hl a b]
          cases h : t.act j a b with
          | ret c => exact rfl
          | go z q =>
            refine ⟨rfl, ?_⟩
            rcases htgt j l' hl a b z q h with ⟨l'', hz⟩ | cz
            · exact .inl ⟨rfl, l'', hz⟩
            · exact .inr ⟨cz, cz⟩
        · rw [cj, (hnone j' cj').1]
          exact ⟨rfl, .inr ⟨(hnone j cj).2, cj'⟩⟩⟩ x x (.inl ⟨rfl, l, hx⟩)

end Spun

/-! ## The dulled table and a table with written rows and silent rows -/

theorem dulled_live {M : Nat} (t s : Router M) (cyc : Fin (M + 1) → Bool) (nxt : Fin (M + 1) → Fin (M + 1))
    (live : Fin (M + 1) → Prop)
    (hlive : ∀ y, live y → cyc y = false ∧ s.prog y = t.prog y ∧
      ∀ a b, s.act y a b = dullAct cyc (t.act y a b))
    (htgt : ∀ y, live y → ∀ a b z q, t.act y a b = .go z q → live z ∨ cyc z = true)
    (hspin : ∀ y, cyc y = true →
      s.prog y = .ret 0 0 ∧ (∀ a b, s.act y a b = .go y false) ∧ cyc (nxt y) = true)
    (x : Fin (M + 1)) (hx : live x ∨ cyc x = true) :
    Eqv false [State] ((dulled t cyc nxt).entered x) (s.entered x) [Bit] :=
  router_bisimulation_eqv (dulled t cyc nxt) s
    (fun j j' => (j = j' ∧ live j) ∨ (cyc j = true ∧ cyc j' = true))
    ⟨fun j j' r => by
        show dullProg (cyc j) (t.prog j) = s.prog j'
        rcases r with ⟨e, lj⟩ | ⟨cj, cj'⟩
        · subst e
          rw [(hlive j lj).1, (hlive j lj).2.1]
          rfl
        · rw [cj, (hspin j' cj').1]
          rfl,
      fun j j' r a b => by
        show Act.Rel _ (dullRow cyc (cyc j) (nxt j) (t.act j) a b) (s.act j' a b)
        rcases r with ⟨e, lj⟩ | ⟨cj, cj'⟩
        · subst e
          rw [(hlive j lj).1, (hlive j lj).2.2 a b]
          show Act.Rel _ (dullAct cyc (t.act j a b)) (dullAct cyc (t.act j a b))
          cases h : t.act j a b with
          | ret c => exact rfl
          | go z q =>
            refine ⟨rfl, ?_⟩
            rcases htgt j lj a b z q h with lz | cz
            · exact .inl ⟨rfl, lz⟩
            · exact .inr ⟨cz, cz⟩
        · rw [cj, (hspin j' cj').2.1 a b]
          exact ⟨rfl, .inr ⟨(hspin j cj).2.2, cj'⟩⟩⟩ x x
    (hx.elim (fun l => .inl ⟨rfl, l⟩) (fun c => .inr ⟨c, c⟩))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
