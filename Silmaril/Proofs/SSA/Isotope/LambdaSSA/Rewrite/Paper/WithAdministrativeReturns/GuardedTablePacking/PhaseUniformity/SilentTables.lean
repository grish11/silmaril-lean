module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentElim

/-! # Mixed tables: request-free rows composed into the split request trees -/

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
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

/-! ## A request-free row, in default Paper -/

/-- A request-free row entered with a constant is the action of its exit
on that constant. -/
theorem pure_const (M : Nat) (e : Fin 2) (a : Bool → Bool → Act M) (g : Bool) :
    ofRegion (seqValueBranches (const_typed g) (routerRow_typed M (.ret e 0) a)) =
      ofRegion (act_typed M (a (exitBit e) g)) :=
  ((row_packed (routerRoute_typed M a) g (.ret e 0)).trans
    (congrArg (· ≫ ofRegion (routerRoute_typed M a))
      (region_arrow_congr (envCode_const (.ret e 0) g) _ (envSpec_typed (.ret e 0) fun _ => g)))).trans
    (leaf_arrow M a e 0 fun _ => g)

theorem pure_const_mix {K : Nat} (m : MixRow) {e : Fin 2} (hm : m = .pure e) (a₀ : Bool → Bool → Act K)
    (g : Bool) :
    ofRegion (seqValueBranches (const_typed g)
      (routerRow_typed (K + (K + 1)) m.program fun a b => redirect (m.act K a₀ a b))) =
      ofRegion (act_typed (K + (K + 1)) (redirect (a₀ (exitBit e) g))) := by
  subst hm
  exact pure_const (K + (K + 1)) e (fun a b => redirect (a₀ (exitBit e) b)) g

/-! ## The silent states of the split mixed table -/

section Sil

variable {K : Nat}

theorem silent_some {m : MixRow} {a : Bool → Bool → Act K} {g : Bool} {A : Act (K + (K + 1))}
    (h : m.silent a g = some A) : ∃ e, m = .pure e ∧ A = redirect (a (exitBit e) g) := by
  cases m with
  | ask r => cases h
  | pure e => exact ⟨e, rfl, (Option.some.inj h).symm⟩

theorem silent_none {m : MixRow} {a : Bool → Bool → Act K} {g : Bool} (h : m.silent a g = none) :
    ∃ r, m = .ask r := by
  cases m with
  | ask r => exact ⟨r, rfl⟩
  | pure e => cases h

theorem redirect_go {a : Act K} {z : Fin (K + (K + 1) + 1)} {q : Bool} (h : redirect a = .go z q) :
    ∃ j, a = .go j q ∧ z = splitIdx j q := by
  cases a with
  | ret b => cases h
  | go j q' =>
    cases h
    exact ⟨j, rfl, rfl⟩

variable (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem mix_hsil (y : Fin (K + (K + 1) + 1)) (A : Act (K + (K + 1))) (h : mixSil row act y = some A) :
    ofRegion (seqValueBranches (const_typed (splitBit y)) ((splitRouter (mixRouter row act)).rows_typed y)) =
      ofRegion (act_typed (K + (K + 1)) A) := by
  obtain ⟨e, hm, rfl⟩ := silent_some h
  exact pure_const_mix (row (splitRow y)) hm (act (splitRow y)) (splitBit y)

theorem mix_hcar (y : Fin (K + (K + 1) + 1)) (A : Act (K + (K + 1))) (h : mixSil row act y = some A) :
    A.Carries splitBit := by
  obtain ⟨e, -, rfl⟩ := silent_some h
  exact redirect_carries _

theorem mix_hact (x : Fin (K + (K + 1) + 1)) (a b : Bool) :
    ((splitRouter (mixRouter row act)).act x a b).Carries splitBit :=
  redirect_carries _

variable {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

include hr in
/-- The ranking resolves every action within the fuel. -/
theorem mix_settled (a : Act (K + (K + 1))) : (resolveN (mixSil row act) fuel a).Settled (mixSil row act) :=
  ranked_settled (mixSil row act) (rank := fun y => rank (splitRow y) (splitBit y))
    (fun y A hy z q hA B hz => by
      obtain ⟨e, hm, rfl⟩ := silent_some hy
      obtain ⟨j, hj, rfl⟩ := redirect_go hA
      obtain ⟨e', hm', -⟩ := silent_some hz
      rw [splitRow_idx] at hm'
      have down := hr.2 (splitRow y) (splitBit y) e hm j q hj e' hm'
      show rank (splitRow (splitIdx j q)) (splitBit (splitIdx j q)) < _
      rw [splitRow_idx, splitBit_idx]
      exact down)
    fuel a (fun y _ _ _ _ => hr.1 _ _)

end Sil

/-! ## Rows of the fragment at states that carry a Bit -/

section Carried

variable {M : Nat} (c : Fin (M + 1) → Bool) (rows : Fin (M + 1) → EnvRow)
  (act : Fin (M + 1) → Bool → Bool → Act M) (hc : ∀ x a b, (act x a b).Carries c)

include hc in
/-- Entered with the Bit its state carries, a table of rows of the
fragment is its table of literal request trees. -/
theorem carried_const (x : Fin (M + 1)) :
    QLit (const_typed (c x)) ≫ QLit ((envRouter rows act).entered_typed x) =
      QLit (const_typed (c x)) ≫ QLit ((kidsTable c rows act).entered_typed x) := by
  have m₁ : Matched c (envRouter rows act).rows_typed := router_matched c (envRouter rows act) hc
  have m₂ : Matched c (kidsTable c rows act).toTable.rows_typed :=
    ltable_matched c (kidsTable c rows act) fun x a b => by
      cases a
      · exact envTree_carries c _ (hc x) (rows x).left _
      · exact envTree_carries c _ (hc x) (rows x).right _
  have tables := (Paper.Extension.Singleton.ofRegion_eq_iff N
    (dispatchEntered_typed (resetRows_typed c (envRouter rows act).rows_typed) x)
    (dispatchEntered_typed (resetRows_typed c (kidsTable c rows act).toTable.rows_typed) x)).2
    (dispatch_rows_eqv (resetRows_typed c (envRouter rows act).rows_typed)
      (resetRows_typed c (kidsTable c rows act).toTable.rows_typed)
      (fun i => q_reset_congr (c i) ((envRouter rows act).rows_typed i)
        ((kidsTable c rows act).toTable.rows_typed i) (env_row_const M (rows i) (act i) (c i))) x)
  have a := congrArg (π).map (reset_entered c (envRouter rows act).rows_typed m₁ x)
  have b := congrArg (π).map (reset_entered c (kidsTable c rows act).toTable.rows_typed m₂ x)
  rw [(π).map_comp] at a b
  have reset : QLit (reset_typed (c x)) ≫ QLit ((envRouter rows act).entered_typed x) =
      QLit (reset_typed (c x)) ≫ QLit ((kidsTable c rows act).toTable.entered_typed x) :=
    a.symm.trans (tables.trans b)
  have pre : ∀ f : (π).obj (ofType (Φ := signature.Instr) State) ⟶ (π).obj (ofType Bit),
      QLit (const_typed (c x)) ≫ f = QLit (const_typed (c x)) ≫ QLit (reset_typed (c x)) ≫ f := fun f =>
    ((congrArg (· ≫ f) (q_const_reset (c x))).symm.trans (Category.assoc _ _ _))
  exact (pre _).trans ((congrArg (QLit (const_typed (c x)) ≫ ·) reset).trans (pre _).symm)

end Carried

/-! ## The request rows of the resolved table -/

section Source

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

theorem ask_program {m : MixRow} {r : EnvRow} (h : m = .ask r) : m.program = m.envRow.program := by
  subst h
  rfl

theorem ask_act {M : Nat} {m : MixRow} {r : EnvRow} (h : m = .ask r) (sil : Fin (M + 1) → Option (Act M))
    (n : Nat) (x : Fin (M + 1)) (g : Bool) (a₀ : Bool → Bool → Act K) (ρ : Act K → Act M) (a b : Bool) :
    resolveN sil n (ρ (m.act K a₀ a b)) = m.settledAct sil n x g (fun a b => ρ (a₀ a b)) a b := by
  subst h
  rfl

theorem rel_settled {M : Nat} (sil : Fin (M + 1) → Option (Act M)) (a : Act M) (h : a.Settled sil) :
    Act.Rel (fun x y => x = y ∧ sil x = none) a a := by
  cases a with
  | ret b => exact rfl
  | go y q => exact ⟨rfl, rfl, h⟩

theorem settledAct_carries (m : MixRow) (x : Fin (K + (K + 1) + 1)) (a₀ : Bool → Bool → Act (K + (K + 1)))
    (h₀ : ∀ a b, (a₀ a b).Carries splitBit) (a b : Bool) :
    (m.settledAct (mixSil row act) fuel x (splitBit x) a₀ a b).Carries splitBit := by
  cases m with
  | ask r => exact resolve_carries (mixSil row act) splitBit (mix_hcar row act) fuel _ (h₀ a b)
  | pure e => exact rfl

include hr in
/-- At a state that sends a request, the resolved table is the table of
resolved request rows. A bisimulation: no resolved action reaches a
request-free row. -/
theorem resolved_rows (y : Fin (K + (K + 1) + 1)) (hy : mixSil row act y = none) :
    Eqv false [State] (((splitRouter (mixRouter row act)).resolved (mixSil row act) fuel).entered y)
      ((envRouter (fun x => (row (splitRow x)).envRow) (mixAct row act fuel)).entered y) [Bit] :=
  router_bisimulation_eqv _ _ (fun x y => x = y ∧ mixSil row act x = none)
    ⟨fun x y ⟨e, hx⟩ => by
        subst e
        obtain ⟨r, hm⟩ := silent_none hx
        exact ask_program hm,
      fun x y ⟨e, hx⟩ a b => by
        subst e
        obtain ⟨r, hm⟩ := silent_none hx
        have same := ask_act hm (mixSil row act) fuel x (splitBit x) (act (splitRow x)) redirect a b
        show Act.Rel (fun x y => x = y ∧ mixSil row act x = none)
          (resolveN (mixSil row act) fuel (redirect ((row (splitRow x)).act K (act (splitRow x)) a b)))
          ((row (splitRow x)).settledAct (mixSil row act) fuel x (splitBit x)
            (fun a b => redirect (act (splitRow x) a b)) a b)
        rw [← same]
        exact rel_settled (mixSil row act) _
          (mix_settled row act hr (redirect ((row (splitRow x)).act K (act (splitRow x)) a b)))⟩ y y ⟨rfl, hy⟩

include hr in
/-- Entered with the Bit its state carries, the resolved table at a state
that sends a request is the table of literal request trees. -/
theorem resolved_source (y : Fin (K + (K + 1) + 1)) (hy : mixSil row act y = none) :
    QLit (const_typed (splitBit y)) ≫
        QLit (((splitRouter (mixRouter row act)).resolved (mixSil row act) fuel).entered_typed y) =
      QLit (const_typed (splitBit y)) ≫ QLit ((mixSource row act fuel).entered_typed y) :=
  (congrArg (QLit (const_typed (splitBit y)) ≫ ·)
    ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (resolved_rows row act hr y hy))).trans
    (carried_const splitBit (fun x => (row (splitRow x)).envRow) (mixAct row act fuel)
      (fun x a b => settledAct_carries row act (row (splitRow x)) x _ (fun _ _ => redirect_carries _) a b) y)

end Source

/-! ## The original entries -/

section Landed

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

include hr in
/-- A resolved action continued in the resolved table is its landing. -/
theorem landing_arrow (a : Act (K + (K + 1))) (hs : a.Settled (mixSil row act)) (hc : a.Carries splitBit) :
    (π).map (Act.arrow ((splitRouter (mixRouter row act)).resolved (mixSil row act) fuel) a) =
      QLit (Landing.region_typed (a.landing (mixSource row act fuel))) := by
  cases a with
  | ret b => rw [arrow_ret]
  | go y q =>
    have cy : splitBit y = q := hc
    subst cy
    rw [arrow_go]
    exact ((π).map_comp _ _).trans ((resolved_source row act hr y hs).trans
      (q_const (splitBit y) ((mixSource row act fuel).entered_typed y)).symm)

include hr in
/-- The mixed table entered with each constant is its landing: a returned
Bit, or the table of literal request trees entered at a request row. -/
theorem mix_landed (j : Fin (K + 1)) :
    Landed ((mixRouter row act).entered j) (mixLanding row act fuel j) := fun q => by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q ((mixRouter row act).entered_typed j))
    (Landing.region_typed (mixLanding row act fuel j q))).1
  have fold : QLit ((splitRouter (mixRouter row act)).entered_typed (splitIdx j q)) =
      QLit ((mixRouter row act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (router_split_fold (mixRouter row act) j q)
  have entry := silent_entry (splitRouter (mixRouter row act)) splitBit (mixSil row act) fuel
    (mix_hsil row act) (mix_hcar row act) (mix_hact row act)
    (fun x a b => mix_settled row act hr _) (splitIdx j q) (mix_settled row act hr _)
  rw [splitBit_idx] at entry
  have settled := mix_settled row act hr (.go (splitIdx j q) q)
  have carries := resolve_carries (mixSil row act) splitBit (mix_hcar row act) fuel
    (.go (splitIdx j q) q) (splitBit_idx j q)
  exact (q_const q ((mixRouter row act).entered_typed j)).trans
    ((congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
      ((((π).map_comp _ _).symm.trans (congrArg (π).map entry)).trans
        (landing_arrow row act hr _ settled carries)))

end Landed

/-! ## Loops with landings -/

section Landings

variable {M M' : Nat}

theorem landing_region_eqv {L : Landing M} {L' : Landing M'} (h : L.Rel L') :
    Eqv false [U] L.region L'.region [Bit] := by
  cases L with
  | ret b =>
    cases L' with
    | ret b' =>
      have e : b = b' := h
      subst e
      exact Paper.Extension.Eqv.refl (Landing.region_typed (M := M) (.ret b)).hasType
    | «at» t' x' q' => exact h.elim
    | spin => exact h.elim
  | «at» t x q =>
    cases L' with
    | ret b' => exact h.elim
    | «at» t' x' q' =>
      obtain ⟨e, eq⟩ : q = q' ∧ Eqv false [State] (t.entered x) (t'.entered x') [Bit] := h
      subst e
      exact (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (t.entered_typed x))
        (constEntry_typed q (t'.entered_typed x'))).1
        ((q_const q (t.entered_typed x)).trans ((congrArg (QLit (const_typed q) ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed x) (t'.entered_typed x')).2 eq)).trans
            (q_const q (t'.entered_typed x')).symm))
    | spin => exact h.elim
  | spin =>
    cases L' with
    | ret b' => exact h.elim
    | «at» t' x' q' => exact h.elim
    | spin => exact Paper.Extension.Eqv.refl spinRegion_typed.hasType

variable {r r' : Region signature.Instr} {L : Bool → Landing M} {L' : Bool → Landing M'}

/-- A loop is the case on its state of its two landings. -/
theorem landed_case (h : ValueBranches [State] r [Bit]) (hl : Landed r L) :
    Eqv false [State] r (caseEntry (L false).region (L true).region) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N h
    (caseEntry_typed (Landing.region_typed (L false)) (Landing.region_typed (L true)))).1
  have point : ∀ q, QLit (constEntry_typed q h) = QLit (Landing.region_typed (L q)) := fun q =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (hl q)
  exact (congrArg (π).map (state_eta h)).trans
    (q_case_congr (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)) deadBit_typed
      (caseValueBranches (Landing.region_typed (L false)) (Landing.region_typed (L true))) deadBit_typed
      (q_case_congr (constEntry_typed false h) (constEntry_typed true h) (Landing.region_typed (L false))
        (Landing.region_typed (L true)) (point false) (point true)) rfl)

/-- Two loops whose landings agree at each constant are equal. -/
theorem landed_eqv (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L') (rel : ∀ q, (L q).Rel (L' q)) : Eqv false [State] r r' [Bit] := by
  refine (landed_case h hl).trans (Paper.Extension.Eqv.trans ?_ (landed_case h' hl').symm)
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N
    (caseEntry_typed (Landing.region_typed (L false)) (Landing.region_typed (L true)))
    (caseEntry_typed (Landing.region_typed (L' false)) (Landing.region_typed (L' true)))).1
  have point : ∀ q, QLit (Landing.region_typed (L q)) = QLit (Landing.region_typed (L' q)) := fun q =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (landing_region_eqv (rel q))
  exact q_case_congr (caseValueBranches (Landing.region_typed (L false)) (Landing.region_typed (L true)))
    deadBit_typed (caseValueBranches (Landing.region_typed (L' false)) (Landing.region_typed (L' true)))
    deadBit_typed (q_case_congr _ _ _ _ (point false) (point true)) rfl

end Landings

/-- Landings transfer along an equation of the quotient. -/
theorem landed_congr {M : Nat} {r r' : Region signature.Instr} {L : Bool → Landing M}
    (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (e : Eqv false [State] r r' [Bit]) (hl : Landed r' L) : Landed r L := fun q =>
  (Paper.Extension.Eqv.trans
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h) (constEntry_typed q h')).1
      ((q_const q h).trans ((congrArg (QLit (const_typed q) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N h h').2 e)).trans (q_const q h').symm))) (hl q))

/-- A loop that is literal request trees at each constant lands in them. -/
theorem landed_of_pointed {M : Nat} {r : Region signature.Instr} {t : Bool → LTable M} {x : Bool → Fin (M + 1)}
    (hp : Pointed r t x) : Landed r fun q => .at (t q) (x q) q :=
  fun q => hp q

/-! ## The written table -/

theorem pure_row (M : Nat) (e : Fin 2) (a : Bool → Bool → Act M) :
    ofRegion (routerRow_typed M (.ret e 0) a) =
      ofRegion unpack_typed ≫ ofRegion (bitSplit_typed M (a (exitBit e) false) (a (exitBit e) true)) := by
  have unit : ∀ x : Bool, ofRegion (seqValueBranches idBit (bitSplit_typed M (a x false) (a x true))) =
      ofRegion (bitSplit_typed M (a x false) (a x true)) := fun x =>
    (ofRegion_comp idBit (bitSplit_typed M (a x false) (a x true)) _).symm.trans
      (by rw [ofRegion_id, Category.id_comp])
  have split : ∀ p : Program, ofRegion (routerRow_typed M p a) =
      ofRegion unpack_typed ≫ ofRegion p.typed.packExits ≫ ofRegion (routerRoute_typed M a) := fun p => by
    rw [← ofRegion_comp (step_typed p) (routerRoute_typed M a) (routerRow_typed M p a),
      ← ofRegion_comp unpack_typed p.typed.packExits (step_typed p), Category.assoc]
  match e with
  | 0 =>
    have route : ofRegion brInl_typed ≫ ofRegion (routerRoute_typed M a) =
        ofRegion (bitSplit_typed M (a false false) (a false true)) :=
      (ofRegion_comp brInl_typed (routerRoute_typed M a) _).trans
        ((case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
          (bitSplit_typed M (a false false) (a false true))
          (stateSplit_typed M (a true false) (a true true))).trans (unit false))
    exact (split (.ret 0 0)).trans (congrArg (ofRegion unpack_typed ≫ ·) route)
  | 1 =>
    have route : ofRegion brInrInl_typed ≫ ofRegion (routerRoute_typed M a) =
        ofRegion (bitSplit_typed M (a true false) (a true true)) :=
      (ofRegion_comp brInrInl_typed (routerRoute_typed M a) _).trans
        ((case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr))
          (.inl (.var (i := 0) rfl)) (bitSplit_typed M (a false false) (a false true))
          (stateSplit_typed M (a true false) (a true true))).trans
          ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr))
            (.var (i := 0) rfl) (bitSplit_typed M (a true false) (a true true)) (dead_typed M)).trans
            (unit true)))
    exact (split (.ret 1 0)).trans (congrArg (ofRegion unpack_typed ≫ ·) route)

/-- The table as written and the table with the unused exits rerouted
have the same entered loops, in default Paper. -/
theorem mix_written_arrow {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((mixWritten row act).entered_typed j) = ofRegion ((mixRouter row act).entered_typed j) :=
  dispatch_rows_arrow (mixWritten row act).rows_typed (mixRouter row act).rows_typed (fun i => by
    show ofRegion (routerRow_typed K (row i).program (act i)) =
      ofRegion (routerRow_typed K (row i).program ((row i).act K (act i)))
    cases row i with
    | ask r => rfl
    | pure e => exact (pure_row K e (act i)).trans (pure_row K e fun _ g => act i (exitBit e) g).symm) j

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
