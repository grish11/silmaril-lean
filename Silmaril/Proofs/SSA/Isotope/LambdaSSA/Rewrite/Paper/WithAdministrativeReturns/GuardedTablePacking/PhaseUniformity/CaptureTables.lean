module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptureConstant
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Thms

/-! # A kept Bit: request trees, tables, completeness and the regression -/

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
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)

/-! ## The request trees -/

theorem q_region_congr {X D : Ty Empty} {r r' : Region signature.Instr} (e : r = r')
    (h : ValueBranches [X] r [D]) (h' : ValueBranches [X] r' [D]) : QLit h = QLit h' := by
  subst e
  rfl

section Ask

variable {K : Nat} {r : Bool → Bool → Region signature.Instr}
  (h : ∀ x y, ValueBranches [U] (r x y) [Silmaril.coprod Bit (States K)])

/-- A request sent with a constant query is the constant followed by the
packed program and the routing, in default Paper. -/
theorem ask_packed (q : Bool) (p : Program) :
    ofRegion (seqValueBranches (const_typed q) (genRow_typed p h)) =
      ofRegion (seqValueBranches (bit_typed q) p.typed.packExits) ≫ ofRegion (genRoute_typed h) := by
  have a := (ofRegion_comp (const_typed q) (genRow_typed p h)
    (seqValueBranches (const_typed q) (genRow_typed p h))).symm
  have b := (ofRegion_comp (step_typed p) (genRoute_typed h) (genRow_typed p h)).symm
  have c := (ofRegion_comp unpack_typed p.typed.packExits (step_typed p)).symm
  have d := (ofRegion_comp (bit_typed q) p.typed.packExits
    (seqValueBranches (bit_typed q) p.typed.packExits)).symm
  rw [a, b, c, d, const_arrow q]
  simp only [Category.assoc]
  rw [← Category.assoc (ofRegion bitState_typed), pack_unpack, Category.id_comp]

/-- If a packed program entered with the constant `y` is another packed
program entered with `y` with its returned payload fixed to `y`, then the
first sent with `y` is the second sent with `y` whose left result is the
result at `y`. In the quotient. -/
theorem fixed_ask_region (y : Bool) {p p' : Program}
    (fx : QLit (seqValueBranches (bit_typed y) p.typed.packExits) =
      QLit (seqValueBranches (seqValueBranches (bit_typed y) p'.typed.packExits) (fix_typed y))) :
    QLit (seqValueBranches (const_typed y) (genRow_typed p h)) =
      QLit (seqValueBranches (const_typed y) (genRow_typed p' (kept_typed h y))) := by
  calc
    QLit (seqValueBranches (const_typed y) (genRow_typed p h)) =
        QLit (seqValueBranches (bit_typed y) p.typed.packExits) ≫ QLit (genRoute_typed h) :=
      (congrArg (π).map (ask_packed h y p)).trans ((π).map_comp _ _)
    _ = (QLit (seqValueBranches (bit_typed y) p'.typed.packExits) ≫ QLit (fix_typed y)) ≫
          QLit (genRoute_typed h) := by
      rw [fx, q_comp (seqValueBranches (bit_typed y) p'.typed.packExits) (fix_typed y)]
    _ = QLit (seqValueBranches (bit_typed y) p'.typed.packExits) ≫
          QLit (genRoute_typed (kept_typed h y)) := by
      rw [Category.assoc, fix_route h y]
    _ = QLit (seqValueBranches (const_typed y) (genRow_typed p' (kept_typed h y))) :=
      (((π).map_comp _ _).symm.trans (congrArg (π).map (ask_packed (kept_typed h y) y p').symm))

end Ask

/-- The same on trees: a request node whose program is fixed in this way. -/
theorem fixed_ask (K : Nat) (y : Bool) {p p' : Program}
    (fx : QLit (seqValueBranches (bit_typed y) p.typed.packExits) =
      QLit (seqValueBranches (seqValueBranches (bit_typed y) p'.typed.packExits) (fix_typed y)))
    (kids : Bool → Bool → Tree K) :
    QLit (treeRegion_typed K (.ask y p kids)) = QLit (treeRegion_typed K (.ask y p' (keptKids kids y))) :=
  (fixed_ask_region (fun x y => treeRegion_typed K (kids x y)) y fx).trans
    (q_region_congr (congrArg (fun k => (Region.br 0 (.inl (bitTm y))).lsubst
        (fun _ => (genRow p' k).renameVars (Silmaril.DeBruijn.lift Nat.succ)))
      (funext fun x' => funext fun y' => by cases x' <;> rfl)) _ _)

/-- The second step sent with the constant `y` is the labelled request
sent with `y` whose left reply takes the tree at `y`. -/
theorem kept_ask (K : Nat) (l₂ y : Bool) (kids : Bool → Bool → Tree K) :
    QLit (treeRegion_typed K (.ask y (capSecond l₂) kids)) =
      QLit (treeRegion_typed K (.ask y (labelPoll l₂).program (keptKids kids y))) :=
  fixed_ask K y (cap_fix l₂ y) kids

/-- The program that keeps its entry state sent with the constant `g` is
the two-request program sent with `g` whose return takes the tree at `g`. -/
theorem entry_ask (K : Nat) (l₁ l₂ g : Bool) (kids : Bool → Bool → Tree K) :
    QLit (treeRegion_typed K (.ask g (entryProgram l₁ l₂) kids)) =
      QLit (treeRegion_typed K (.ask g (duoProgram l₁ l₂) (keptKids kids g))) :=
  fixed_ask K g (entry_fix l₁ l₂ g) kids

/-! ## Rows and tables, in the quotient -/

/-- Rows with equal result regions in the quotient are equal there. -/
theorem q_genRow_congr {K : Nat} (p : Program) {r r' : Bool → Bool → Region signature.Instr}
    (h : ∀ x y, ValueBranches [U] (r x y) [Silmaril.coprod Bit (States K)])
    (h' : ∀ x y, ValueBranches [U] (r' x y) [Silmaril.coprod Bit (States K)])
    (e : ∀ x y, QLit (h x y) = QLit (h' x y)) : QLit (genRow_typed p h) = QLit (genRow_typed p h') := by
  have route : QLit (genRoute_typed h) = QLit (genRoute_typed h') :=
    q_case_congr (caseValueBranches (h false false) (h false true))
      (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))
      (caseValueBranches (h' false false) (h' false true))
      (caseValueBranches (caseValueBranches (h' true false) (h' true true)) (dead_typed K))
      (q_case_congr (h false false) (h false true) (h' false false) (h' false true) (e false false)
        (e false true))
      (q_case_congr (caseValueBranches (h true false) (h true true)) (dead_typed K)
        (caseValueBranches (h' true false) (h' true true)) (dead_typed K)
        (q_case_congr (h true false) (h true true) (h' true false) (h' true true) (e true false)
          (e true true)) rfl)
  exact (q_comp (step_typed p) (genRoute_typed h)).trans
    ((congrArg (QLit (step_typed p) ≫ ·) route).trans (q_comp (step_typed p) (genRoute_typed h')).symm)

/-- The row of the program that keeps its first reply is the row of
literal request trees that act on the kept payload. -/
theorem cap_row (K : Nat) (l₁ l₂ : Bool) (a : Bool → Bool → Act K) :
    QLit (routerRow_typed K (capProgram l₁ l₂) a) =
      QLit (genRow_typed (labelPoll l₁).program
        fun x y => treeRegion_typed K (selKids K l₂ a keepFirst x y).toTree) := by
  refine (congrArg (π).map (factored_row K (cap_step_arrow l₁ l₂) a)).trans ?_
  refine q_genRow_congr (labelPoll l₁).program
    (fun x y => treeRegion_typed K (duoKids K (capSecond l₂) a x y))
    (fun x y => treeRegion_typed K (selKids K l₂ a keepFirst x y).toTree) fun x y => ?_
  cases x
  · exact (kept_ask K l₂ y fun x' y' => .leaf (a x' y')).trans
      (q_region_congr (congrArg (fun k => treeRegion K (.ask y (labelPoll l₂).program k))
        (funext fun x' => funext fun y' => by cases x' <;> rfl)) _ _)
  · rfl

/-- The table of programs that keep their first reply equals its table of
literal request trees at every entry. -/
theorem cap_table_eqv {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    Eqv false [State] ((capRouter l₁ l₂ act).entered j) ((capSource l₁ l₂ act).entered j) [Bit] :=
  dispatch_rows_eqv (capRouter l₁ l₂ act).rows_typed (capSource l₁ l₂ act).toTable.rows_typed
    (fun i => cap_row K (l₁ i) (l₂ i) (act i)) j

/-! ## Regression: which Bit the second left reply acts on -/

theorem duoSource_sel {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) :
    duoSource l₁ l₂ act = selSource useSecond l₁ l₂ act :=
  congrArg (LTable.mk l₁) (funext fun i => funext fun x => funext fun y => by
    cases x
    · exact congrArg (LTree.ask y (l₂ i)) (funext fun x' => funext fun y' => by cases x' <;> rfl)
    · rfl)

theorem sel_nest (l₁ l₂ : Bool) (sel : Bool → Bool → Bool) :
    (selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).toTable =
      TreeTable.nest (K := 0) 2 (Router.ofLabels (selExplicitLabel l₁ l₂) (selExplicitAct sel)).toTrees := by
  have progs : (selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).toTable.prog =
      (TreeTable.nest (K := 0) 2
        (Router.ofLabels (selExplicitLabel l₁ l₂) (selExplicitAct sel)).toTrees).prog := by
    funext j
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    rfl
  have kids : (selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).toTable.kids =
      (TreeTable.nest (K := 0) 2
        (Router.ofLabels (selExplicitLabel l₁ l₂) (selExplicitAct sel)).toTrees).kids := by
    funext j x y
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    cases x <;> cases y <;> first
      | rfl
      | (refine congrArg (Tree.ask _ _) (funext fun x' => funext fun y' => ?_)
         cases x' <;> cases y' <;> rfl)
  exact (congrArg (fun k => TreeTable.mk (selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).toTable.prog k)
    kids).trans (congrArg (fun p => TreeTable.mk p _) progs)

theorem sel_forward (l₁ l₂ : Bool) (sel : Bool → Bool → Bool) :
    (Router.ofLabels (selExplicitLabel l₁ l₂) (selExplicitAct sel)).Forward 2 := by
  intro k hk x y
  match k, hk with
  | 0, _ => cases x <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 1, _ => cases x <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 2, hk => exact absurd hk (by decide)

/-- The literal trees equal the table with the second request as two
explicit states, one for each kept Bit. -/
theorem sel_eqv_explicit (l₁ l₂ : Bool) (sel : Bool → Bool → Bool) :
    Eqv false [State] ((selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((Router.ofLabels (selExplicitLabel l₁ l₂) (selExplicitAct sel)).entered 2) [Bit] := by
  show Eqv false [State] ((selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).toTable.entered 0) _ [Bit]
  rw [sel_nest]
  exact router_nest_eqv (K := 0) 2 _ (sel_forward l₁ l₂ sel) 0

/-- A bisimulation of two such tables at their rows forces the same
choice of Bit. -/
theorem sel_of_bisim (l₁ l₂ : Bool) (sel sel' : Bool → Bool → Bool)
    (h : ∃ R : Fin 3 → Fin 3 → Prop,
      (∀ x y, R x y → selExplicitLabel l₁ l₂ x = selExplicitLabel l₁ l₂ y) ∧
      (∀ x y, R x y → ∀ tag pl, Act.Rel R (selExplicitAct sel x tag pl) (selExplicitAct sel' y tag pl)) ∧
      R 2 2) : sel = sel' := by
  obtain ⟨R, _, ha, r⟩ := h
  funext y y'
  cases y
  · have s : R 0 0 := (ha 2 2 r false false).2
    exact ha 0 0 s false y'
  · have s : R 1 1 := (ha 2 2 r false true).2
    exact ha 1 1 s false y'

/-- Two such tables are equal at their rows exactly when they act on the
same Bit. -/
theorem sel_eqv_iff (l₁ l₂ : Bool) (sel sel' : Bool → Bool → Bool) :
    Eqv false [State] ((selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((selSource sel' (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] ↔ sel = sel' :=
  ⟨fun e => sel_of_bisim l₁ l₂ sel sel' ((Router.labels_eqv_iff _ _ _ _ _ _).1
      ((sel_eqv_explicit l₁ l₂ sel).symm.trans (e.trans (sel_eqv_explicit l₁ l₂ sel')))),
    fun h => h ▸ Paper.Extension.Eqv.refl (LTable.entered_typed _ 0).hasType⟩

/-- Erasing the kept Bit is observable: the program that keeps its first
reply differs from the two-request program that returns the second. -/
theorem cap_ne_duo (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((capRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((duoRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] := fun e => by
  have duo := duo_table_eqv (fun _ : Fin 1 => l₁) (fun _ => l₂) echoAct (fun _ => duo_stepFactors l₁ l₂) 0
  rw [duoSource_sel] at duo
  exact Bool.false_ne_true (congrFun (congrFun ((sel_eqv_iff l₁ l₂ keepFirst useSecond).1
    ((cap_table_eqv _ _ _ 0).symm.trans (e.trans duo))) false) true)

/-- Substituting the wrong constant for the kept Bit is observable. -/
theorem cap_ne_flipped (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((capRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((selSource flipFirst (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] := fun e =>
  Bool.false_ne_true (congrFun (congrFun ((sel_eqv_iff l₁ l₂ keepFirst flipFirst).1
    ((cap_table_eqv _ _ _ 0).symm.trans e)) false) false)

/-! ## Completeness through literal sources -/

/-- The tree form of `kept_ask` as an equation of the quotient. -/
theorem kept_ask_eqv (K : Nat) (l₂ y : Bool) (kids : Bool → Bool → Tree K) :
    Eqv false [U] (treeRegion K (.ask y (capSecond l₂) kids))
      (treeRegion K (.ask y (labelPoll l₂).program (keptKids kids y))) [Silmaril.coprod Bit (States K)] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (treeRegion_typed K (.ask y (capSecond l₂) kids))
    (treeRegion_typed K (.ask y (labelPoll l₂).program (keptKids kids y)))).1 (kept_ask K l₂ y kids)

theorem entry_ask_eqv (K : Nat) (l₁ l₂ g : Bool) (kids : Bool → Bool → Tree K) :
    Eqv false [U] (treeRegion K (.ask g (entryProgram l₁ l₂) kids))
      (treeRegion K (.ask g (duoProgram l₁ l₂) (keptKids kids g))) [Silmaril.coprod Bit (States K)] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (treeRegion_typed K (.ask g (entryProgram l₁ l₂) kids))
    (treeRegion_typed K (.ask g (duoProgram l₁ l₂) (keptKids kids g)))).1 (entry_ask K l₁ l₂ g kids)

/-- Loops equal to literal sources are equal exactly when they are valid
in every supported model. -/
theorem sources_complete {K₁ K₂ : Nat} {r₁ r₂ : Region signature.Instr}
    (h₁ : ValueBranches [State] r₁ [Bit]) (h₂ : ValueBranches [State] r₂ [Bit]) (t₁ : LTable K₁)
    (t₂ : LTable K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (E₁ : Eqv false [State] r₁ (t₁.entered i₁) [Bit]) (E₂ : Eqv false [State] r₂ (t₂.entered i₂) [Bit]) :
    Eqv false [State] r₁ r₂ [Bit] ↔ Valid h₁.hasType h₂.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => E₁.trans (((LTable.eqv_iff_valid t₁ t₂ i₁ i₂).2
      (Valid.trans
        (Valid.symm
          (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false E₁ _ _))
        (Valid.trans v
          (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false E₂
            _ _)))).trans E₂.symm)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
