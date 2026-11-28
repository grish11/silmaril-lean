module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EnvSubst

/-! # Written rows with an environment: request trees, split tables, and the original entries -/

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

/-! ## One request of a schedule on constants -/

theorem push_split {n : Nat} (env : Fin n → Bool) (b : Bool) :
    (fun i => (pushTm (fun i => bitTm (env i)) i).subst (splitSubst b)) = fun i => bitTm (consBit b env i) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · show ((bitTm (env i)).rename Nat.succ).subst (splitSubst b) = bitTm (env i)
    cases env i <;> rfl

theorem liftRen {A B C : Ty Empty} : Ren [A] [A, B, C] (lift Nat.succ) := fun i _ h => by
  cases i with
  | zero => exact h
  | succ i => cases h

/-- A request of a schedule on constants is the labelled request sent
with the constant in its slot, followed by the routing of the schedules
of its replies. Unit η enters through `bit_split`. -/
theorem ask_spec {n : Nat} (l : Bool) (s : Fin n) (left right : Normal 2 (n + 1)) (env : Fin n → Bool) :
    QLit (envSpec_typed (.ask l s left right) env) =
      QLit (seqValueBranches (bit_typed (env s)) (labelPoll l).program.typed.packExits) ≫
        QLit (genRouteAny_typed fun x y =>
          envSpec_typed (match x with | false => left | true => right) (consBit y env)) := by
  have push : ∀ i, Tm.BranchValue [Bit, U] (pushTm (fun i => bitTm (env i)) i) Bit := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact .var rfl
    · exact branchValue_succ (bitTm_typed (env i))
  have eq : ∀ (c : Normal 2 (n + 1)) (b : Bool),
      (envSem c (pushTm fun i => bitTm (env i))).substVars (splitSubst b) = envSpec c (consBit b env) :=
    fun c b => (envSem_subst c _ _).trans (congrArg (envSem c) (push_split env b))
  have sl := bit_split (envSem_typed left _ push)
  have sr := bit_split (envSem_typed right _ push)
  rw [eq left false, eq left true] at sl
  rw [eq right false, eq right true] at sr
  have hop : Tm.HasType [U] (.op (.ask l) (bitTm (env s)) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (bitTm_typed (env s)).hasType
  have step : Eqv false [U] (envSpec (.ask l s left right) env)
      (.case (.op (.ask l) (bitTm (env s)))
        (pairSplit (envSpec left (consBit false env)) (envSpec left (consBit true env)))
        (pairSplit (envSpec right (consBit false env)) (envSpec right (consBit true env))))
      [Silmaril.coprod Bit State] := Paper.Extension.Eqv.case hop sl sr
  have split : ∀ c : Normal 2 (n + 1), ValueBranches [Bit, U]
      (pairSplit (envSpec c (consBit false env)) (envSpec c (consBit true env))) [Silmaril.coprod Bit State] :=
    fun c => .case (A := U) (B := U) (.var rfl) ((envSpec_typed c _).renameVars liftRen)
      ((envSpec_typed c _).renameVars liftRen)
  have hs : ValueBranches [U] (.case (.op (.ask l) (bitTm (env s)))
      (pairSplit (envSpec left (consBit false env)) (envSpec left (consBit true env)))
      (pairSplit (envSpec right (consBit false env)) (envSpec right (consBit true env))) :
        Region signature.Instr) [Silmaril.coprod Bit State] := .case hop (split left) (split right)
  have sk := ask_skeleton (X := State) l (env s)
    (r := fun x y => envSpec (match x with | false => left | true => right) (consBit y env))
    (fun x y => envSpec_typed _ _) (fun x y ρ => envSpec_rename _ _ ρ) hs
  exact ((Paper.Extension.Singleton.ofRegion_eq_iff N (envSpec_typed (.ask l s left right) env) hs).2 step).trans
    ((congrArg (π).map sk).trans ((π).map_comp _ _))

/-! ## Leaves -/

/-- A leaf on constants followed by the routing is its action. In default Paper. -/
theorem leaf_arrow (K : Nat) (a : Bool → Bool → Act K) {n : Nat} (e : Fin 2) (s : Fin n) (env : Fin n → Bool) :
    ofRegion (envSpec_typed (.ret e s) env) ≫ ofRegion (routerRoute_typed K a) =
      ofRegion (act_typed K (a (exitBit e) (env s))) := by
  have bits : ∀ x : Bool, ofRegion (seqValueBranches (bit_typed (env s))
      (bitSplit_typed K (a x false) (a x true))) = ofRegion (act_typed K (a x (env s))) := fun x => by
    have c := bit_case (env s) (act_typed K (a x false)) (act_typed K (a x true))
    cases h : env s <;> rw [h] at c <;> exact c
  match e with
  | 0 =>
    exact (ofRegion_comp (envSpec_typed (.ret 0 s) env) (routerRoute_typed K a) _).trans
      ((case_inl_arrow (X := U) (B := State) (t := bitTm (env s)) (bitTm_typed (env s))
        (bitSplit_typed K (a false false) (a false true))
        (stateSplit_typed K (a true false) (a true true))).trans (bits false))
  | 1 =>
    exact (ofRegion_comp (envSpec_typed (.ret 1 s) env) (routerRoute_typed K a) _).trans
      ((case_inr_arrow (X := U) (A := Bit) (t := (.inl (bitTm (env s)) : Tm signature.Instr))
        (.inl (bitTm_typed (env s))) (bitSplit_typed K (a false false) (a false true))
        (stateSplit_typed K (a true false) (a true true))).trans
        ((case_inl_arrow (X := U) (B := Silmaril.empty) (t := bitTm (env s)) (bitTm_typed (env s))
          (bitSplit_typed K (a true false) (a true true)) (dead_typed K)).trans (bits true)))

/-! ## The literal request tree, by induction -/

section Post

variable {A B D E : Ty Empty} {l r l' r' g : Region signature.Instr}

/-- A case followed by a region, with the composites of its arms known. -/
theorem q_case_post (hl : ValueBranches [A] l [D]) (hr : ValueBranches [B] r [D]) (hg : ValueBranches [D] g [E])
    (hl' : ValueBranches [A] l' [E]) (hr' : ValueBranches [B] r' [E])
    (e₁ : QLit hl ≫ QLit hg = QLit hl') (e₂ : QLit hr ≫ QLit hg = QLit hr') :
    QLit (caseValueBranches hl hr) ≫ QLit hg = QLit (caseValueBranches hl' hr') :=
  (((π).map_comp _ _).symm.trans (congrArg (π).map (case_seq_arrow hl hr hg))).trans
    (q_case_congr (seqValueBranches hl hg) (seqValueBranches hr hg) hl' hr' ((q_comp hl hg).trans e₁)
      ((q_comp hr hg).trans e₂))

end Post

/-- A schedule on constants followed by the routing is its literal
request tree. By induction on the schedule. -/
theorem env_tree (K : Nat) (a : Bool → Bool → Act K) : ∀ {n : Nat} (c : Normal 2 n) (env : Fin n → Bool),
    QLit (envSpec_typed c env) ≫ QLit (routerRoute_typed K a) =
      QLit (treeRegion_typed K (envTree a c env).toTree)
  | _, .ret e s, env => ((π).map_comp _ _).symm.trans (congrArg (π).map (leaf_arrow K a e s env))
  | _, .ask l s left right, env => by
    have ih : ∀ x y, QLit (envSpec_typed (match x with | false => left | true => right) (consBit y env)) ≫
        QLit (routerRoute_typed K a) =
        QLit (treeRegion_typed K
          (envTree a (match x with | false => left | true => right) (consBit y env)).toTree) :=
      fun x y => by
        cases x
        · exact env_tree K a left (consBit y env)
        · exact env_tree K a right (consBit y env)
    have dead : QLit (deadAny_typed State) ≫ QLit (routerRoute_typed K a) = QLit (dead_typed K) :=
      ((π).map_comp _ _).symm.trans (congrArg (π).map
        ((ofRegion_comp (deadAny_typed State) (routerRoute_typed K a)
          (seqValueBranches (deadAny_typed State) (routerRoute_typed K a))).trans
          (empty_ext (seqValueBranches (deadAny_typed State) (routerRoute_typed K a)) (dead_typed K))))
    have route : QLit (genRouteAny_typed fun x y =>
          envSpec_typed (match x with | false => left | true => right) (consBit y env)) ≫
        QLit (routerRoute_typed K a) =
        QLit (genRoute_typed fun x y => treeRegion_typed K
          (envTree a (match x with | false => left | true => right) (consBit y env)).toTree) :=
      q_case_post _ _ _ _ _ (q_case_post _ _ _ _ _ (ih false false) (ih false true))
        (q_case_post _ _ _ _ _ (q_case_post _ _ _ _ _ (ih true false) (ih true true)) dead)
    have kids : ∀ x y, ValueBranches [U] (treeRegion K
        (envTree a (match x with | false => left | true => right) (consBit y env)).toTree)
        [Silmaril.coprod Bit (States K)] := fun x y => treeRegion_typed K _
    rw [ask_spec, Category.assoc, route]
    refine (((π).map_comp _ _).symm.trans
      (congrArg (π).map (ask_packed kids (env s) (labelPoll l).program).symm)).trans ?_
    exact q_region_congr (congrArg (fun k => treeRegion K (.ask (env s) (labelPoll l).program k))
      (funext fun x => funext fun y => by cases x <;> rfl)) _ _

/-! ## A written row entered with a constant -/

/-- A written step entered with a constant is the constant followed by the
packed program, in default Paper. -/
theorem row_packed {D : Ty Empty} {g : Region signature.Instr}
    (hg : ValueBranches [Silmaril.coprod Bit State] g [D]) (q : Bool) (p : Program) :
    ofRegion (seqValueBranches (const_typed q) (seqValueBranches (step_typed p) hg)) =
      ofRegion (seqValueBranches (bit_typed q) p.typed.packExits) ≫ ofRegion hg := by
  have a := (ofRegion_comp (const_typed q) (seqValueBranches (step_typed p) hg)
    (seqValueBranches (const_typed q) (seqValueBranches (step_typed p) hg))).symm
  have b := (ofRegion_comp (step_typed p) hg (seqValueBranches (step_typed p) hg)).symm
  have c := (ofRegion_comp unpack_typed p.typed.packExits (step_typed p)).symm
  have d := (ofRegion_comp (bit_typed q) p.typed.packExits
    (seqValueBranches (bit_typed q) p.typed.packExits)).symm
  rw [a, b, c, d, const_arrow q]
  simp only [Category.assoc]
  rw [← Category.assoc (ofRegion bitState_typed), pack_unpack, Category.id_comp]

/-- A written row entered with the constant `c` is the labelled row of
its literal request trees entered with `c`. -/
theorem env_row_const (K : Nat) (r : EnvRow) (a : Bool → Bool → Act K) (c : Bool) :
    QLit (seqValueBranches (const_typed c) (routerRow_typed K r.program a)) =
      QLit (seqValueBranches (const_typed c) (genRow_typed (labelPoll r.label).program
        fun x y => treeRegion_typed K (r.kids a c x y).toTree)) := by
  have packed : ofRegion (seqValueBranches (bit_typed c) r.program.typed.packExits) =
      ofRegion (envSpec_typed r.normal fun _ => c) :=
    region_arrow_congr (envCode_const r.normal c) _ _
  have lhs : QLit (seqValueBranches (const_typed c) (routerRow_typed K r.program a)) =
      QLit (envSpec_typed r.normal fun _ => c) ≫ QLit (routerRoute_typed K a) :=
    (congrArg (π).map ((row_packed (routerRoute_typed K a) c r.program).trans
      (congrArg (· ≫ ofRegion (routerRoute_typed K a)) packed))).trans ((π).map_comp _ _)
  exact lhs.trans ((env_tree K a r.normal fun _ => c).trans
    (q_region_congr (congrArg (fun k => treeRegion K (.ask c (labelPoll r.label).program k))
      (funext fun x => funext fun y => by cases x <;> rfl)) _ _))

/-! ## Trees whose repeats carry the Bit of their target -/

theorem envTree_carries {M : Nat} (cc : Fin (M + 1) → Bool) (a : Bool → Bool → Act M)
    (ha : ∀ x y, (a x y).Carries cc) : ∀ {n : Nat} (c : Normal 2 n) (env : Fin n → Bool),
    (envTree a c env).Carries cc
  | _, .ret e s, env => ha _ _
  | _, .ask l s left right, env => fun x y => by
    cases x
    · exact envTree_carries cc a ha left (consBit y env)
    · exact envTree_carries cc a ha right (consBit y env)

theorem tree_matched {M : Nat} (cc : Fin (M + 1) → Bool) : ∀ (t : LTree M), t.Carries cc →
    (ofRegion (treeRegion_typed M t.toTree) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.map (𝟙 _) (resetArr cc) =
      ofRegion (treeRegion_typed M t.toTree) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom
  | .leaf a, h => act_matched cc a h
  | .ask q l kids, h => by
    have row := gen_post (coprod.map (𝟙 _) (resetArr cc)) (by simp) (labelPoll l).program
      (fun x y => treeRegion_typed M (kids x y).toTree) (fun x y => treeRegion_typed M (kids x y).toTree)
      (fun x y => tree_matched cc (kids x y) (h x y))
    have arrow := ask_arrow M q (labelPoll l).program fun x y => (kids x y).toTree
    show (ofRegion (treeRegion_typed M (.ask q (labelPoll l).program fun x y => (kids x y).toTree)) ≫ _) ≫ _ =
      ofRegion (treeRegion_typed M (.ask q (labelPoll l).program fun x y => (kids x y).toTree)) ≫ _
    rw [arrow]
    simp only [Category.assoc]
    exact congrArg (ofRegion (const_typed q) ≫ ·) ((Category.assoc _ _ _).symm.trans row)

/-- A table of literal request trees all of whose repeats carry the Bit
of their target is matched. -/
theorem ltable_matched {M : Nat} (cc : Fin (M + 1) → Bool) (t : LTable M)
    (h : ∀ x a b, (t.kids x a b).Carries cc) : Matched cc t.toTable.rows_typed :=
  fun x => gen_post (coprod.map (𝟙 _) (resetArr cc)) (by simp) (labelPoll (t.label x)).program
    (fun a b => treeRegion_typed M (t.kids x a b).toTree) (fun a b => treeRegion_typed M (t.kids x a b).toTree)
    (fun a b => tree_matched cc (t.kids x a b) (h x a b))

/-! ## The split of any router table -/

section SplitRouter

variable {K : Nat} (t : Router K)

theorem router_split_matched : Matched splitBit (splitRouter t).rows_typed :=
  router_matched splitBit (splitRouter t) fun x a b => redirect_carries (t.act (splitRow x) a b)

/-- The split table entered at a split state of row `j` is the original
table entered at `j`. The router-morphism fold of the opt-in quotient. -/
theorem router_split_fold (j : Fin (K + 1)) (q : Bool) :
    Eqv false [State] ((splitRouter t).entered (splitIdx j q)) (t.entered j) [Bit] := by
  have hprog : ∀ x, (splitRouter t).prog x = t.prog (splitRow x) := fun _ => rfl
  have hact : ∀ x a b, t.act (splitRow x) a b = ((splitRouter t).act x a b).map splitRow :=
    fun x a b => (redirect_row (t.act (splitRow x) a b)).symm
  have fold := router_morphism_eqv (splitRouter t) t splitRow hprog hact (splitIdx j q)
  rwa [splitRow_idx] at fold

end SplitRouter

/-! ## The split table of written rows -/

section Table

variable {K : Nat} (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem env_source_matched : Matched splitBit (envSource row act).toTable.rows_typed :=
  ltable_matched splitBit (envSource row act) fun x a b => by
    have ha : ∀ a b, (redirect (act (splitRow x) a b)).Carries splitBit := fun a b =>
      redirect_carries (act (splitRow x) a b)
    cases a
    · exact envTree_carries splitBit _ ha (row (splitRow x)).left _
    · exact envTree_carries splitBit _ ha (row (splitRow x)).right _

/-- After the reset, the split table of written rows and the split table
of literal request trees have the same entered loops. -/
theorem env_split_reset (x : Fin (K + (K + 1) + 1)) :
    QLit (reset_typed (splitBit x)) ≫ QLit ((splitRouter (envRouter row act)).entered_typed x) =
      QLit (reset_typed (splitBit x)) ≫ QLit ((envSource row act).toTable.entered_typed x) := by
  have rows := (Paper.Extension.Singleton.ofRegion_eq_iff N
    (dispatchEntered_typed (resetRows_typed splitBit (splitRouter (envRouter row act)).rows_typed) x)
    (dispatchEntered_typed (resetRows_typed splitBit (envSource row act).toTable.rows_typed) x)).2
    (dispatch_rows_eqv (resetRows_typed splitBit (splitRouter (envRouter row act)).rows_typed)
      (resetRows_typed splitBit (envSource row act).toTable.rows_typed)
      (fun i => q_reset_congr (splitBit i) ((splitRouter (envRouter row act)).rows_typed i)
        ((envSource row act).toTable.rows_typed i)
        (env_row_const (K + (K + 1)) (row (splitRow i)) (fun a b => redirect (act (splitRow i) a b))
          (splitBit i))) x)
  have a := congrArg (π).map
    (reset_entered splitBit (splitRouter (envRouter row act)).rows_typed (router_split_matched (envRouter row act)) x)
  have b := congrArg (π).map
    (reset_entered splitBit (envSource row act).toTable.rows_typed (env_source_matched row act) x)
  rw [(π).map_comp] at a b
  exact a.symm.trans (rows.trans b)

/-- The original table is the split table of literal request trees at
each constant. -/
theorem env_pointed (j : Fin (K + 1)) :
    Pointed ((envRouter row act).entered j) (fun _ => envSource row act) (splitIdx j) := fun q => by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q ((envRouter row act).entered_typed j))
    (constEntry_typed q ((envSource row act).entered_typed (splitIdx j q)))).1
  have fold : QLit ((splitRouter (envRouter row act)).entered_typed (splitIdx j q)) =
      QLit ((envRouter row act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (router_split_fold (envRouter row act) j q)
  have reset : QLit (reset_typed q) ≫ QLit ((splitRouter (envRouter row act)).entered_typed (splitIdx j q)) =
      QLit (reset_typed q) ≫ QLit ((envSource row act).toTable.entered_typed (splitIdx j q)) := by
    have r := env_split_reset row act (splitIdx j q)
    rwa [splitBit_idx] at r
  have pre : ∀ f : (π).obj (ofType (Φ := signature.Instr) State) ⟶ (π).obj (ofType Bit),
      QLit (const_typed q) ≫ f = QLit (const_typed q) ≫ QLit (reset_typed q) ≫ f := fun f =>
    ((congrArg (· ≫ f) (q_const_reset q)).symm.trans (Category.assoc _ _ _))
  exact (q_const q ((envRouter row act).entered_typed j)).trans
    (((congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
      ((pre _).trans ((congrArg (QLit (const_typed q) ≫ ·) reset).trans (pre _).symm))).trans
      (q_const q ((envSource row act).entered_typed (splitIdx j q))).symm)

/-- The original table, on an arbitrary state, is the split table of
literal request trees entered by a case on that state. -/
theorem env_case_eqv (j : Fin (K + 1)) :
    Eqv false [State] ((envRouter row act).entered j) (envCase row act j) [Bit] :=
  pointed_eqv ((envRouter row act).entered_typed j) (envCase_typed row act j) (env_pointed row act j)
    (case_pointed (fun _ => envSource row act) (splitIdx j))
    (fun q => Paper.Extension.Eqv.refl ((envSource row act).entered_typed (splitIdx j q)).hasType)

end Table

/-! ## The statements as equations of the quotient -/

theorem env_tree_eqv (K : Nat) (a : Bool → Bool → Act K) {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) :
    Eqv false [U] ((envSpec c env).lsubst fun _ => (routerRoute K a).renameVars (lift Nat.succ))
      (treeRegion K (envTree a c env).toTree) [Silmaril.coprod Bit (States K)] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (seqValueBranches (envSpec_typed c env) (routerRoute_typed K a))
    (treeRegion_typed K (envTree a c env).toTree)).1
    ((q_comp (envSpec_typed c env) (routerRoute_typed K a)).trans (env_tree K a c env))

theorem env_row_const_eqv (K : Nat) (r : EnvRow) (a : Bool → Bool → Act K) (c : Bool) :
    Eqv false [U] (constEntry c (routerRow K r.program a))
      (constEntry c (genRow (labelPoll r.label).program fun x y => treeRegion K (r.kids a c x y).toTree))
      [Silmaril.coprod Bit (States K)] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed c (routerRow_typed K r.program a))
    (constEntry_typed c (genRow_typed (labelPoll r.label).program
      fun x y => treeRegion_typed K (r.kids a c x y).toTree))).1 (env_row_const K r a c)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
