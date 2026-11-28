module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Switch.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableMorphism

/-! # Replay for tables whose successor depends on the reply -/

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

/-! ## The row as an arrow of default Paper -/

/-- The packed state `false`. -/
noncomputable abbrev falseState : ofType (Φ := signature.Instr) Ty.unit ⟶ ofType State :=
  ofRegion (r := .br 0 (.inl (.inl (.var 0)))) (.br rfl (.inl (.inl (.var rfl))))

/-- The Bit `true`. -/
noncomputable abbrev trueBit : ofType (Φ := signature.Instr) Ty.unit ⟶ ofType Bit :=
  ofRegion (r := .br 0 (.inr (.var 0))) (.br rfl (.inr (.var rfl)))

/-- The split of a returned Bit. -/
noncomputable abbrev bitArr (K : Nat) (j : Fin (K + 1)) :
    ofType (Φ := signature.Instr) Bit ⟶ ofType Bit ⨿ ofType (States K) :=
  (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).hom ≫
    coprod.desc (falseState ≫ injArr K j ≫ coprod.inr) (trueBit ≫ coprod.inl)

theorem bitRoute_sum (K : Nat) (j : Fin (K + 1)) :
    ofRegion (bitRoute_typed K j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom = bitArr K j := by
  have arrow : ofRegion (bitRoute_typed K j) =
      (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).hom ≫
        coprod.desc (ofRegion (hold_typed K j)) (ofRegion (leave_typed K)) :=
    (coprod_desc_ofRegion (hold_typed K j) (leave_typed K)).symm
  have hold : ofRegion (hold_typed K j) =
      (falseState ≫ injArr K j) ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    (br_inr (injTm_typed (.inl (.inl (.var rfl))) K j)).trans
      (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv))
        (injOf_eq (.inl (.inl (.var rfl))) K j))
  have leave : ofRegion (leave_typed K) =
      trueBit ≫ (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inl (.inr (.var rfl))
  rw [arrow, hold, leave, Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp

theorem switchRoute_sum (K : Nat) (j₀ j₁ : Fin (K + 1)) :
    ofRegion (switchRoute_typed K j₀ j₁) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫ coprod.desc (bitArr K j₀) (injArr K j₁ ≫ coprod.inr) := by
  have arrow : ofRegion (switchRoute_typed K j₀ j₁) =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫
        coprod.desc (ofRegion (bitRoute_typed K j₀)) (ofRegion (goto_typed K j₁)) :=
    (coprod_desc_ofRegion (bitRoute_typed K j₀) (goto_typed K j₁)).symm
  have goto : ofRegion (goto_typed K j₁) =
      injArr K j₁ ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inr (injTm_typed (.var rfl) K j₁)
  have split := bitRoute_sum K j₀
  rw [arrow, goto, Category.assoc]
  congr 1
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, coprod.inl_desc]
    exact split
  · simp

theorem switchRow_arrow (K : Nat) (p : Program) (j₀ j₁ : Fin (K + 1)) :
    ofRegion (switchRow_typed K p j₀ j₁) = ofRegion (step_typed p) ≫ ofRegion (switchRoute_typed K j₀ j₁) :=
  (Paper.TypeCategory.ofRegion_comp (step_typed p) (switchRoute_typed K j₀ j₁) _).symm

theorem switchRow_sum (K : Nat) (p : Program) (j₀ j₁ : Fin (K + 1)) :
    ofRegion (switchRow_typed K p j₀ j₁) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      stepP p ≫ coprod.desc (bitArr K j₀) (injArr K j₁ ≫ coprod.inr) := by
  rw [switchRow_arrow, Category.assoc, switchRoute_sum, Category.assoc]

variable {K K' : Nat}

theorem switchRow_class (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K'))
    (p p' : Program) (e : p = p') (j₀ j₁ : Fin (K + 1)) (c₀ c₁ : Fin (K' + 1))
    (h₀ : injArr K j₀ ≫ f = injArr K' c₀) (h₁ : injArr K j₁ ≫ f = injArr K' c₁) :
    (ofRegion (switchRow_typed K p j₀ j₁) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (switchRow_typed K' p' c₀ c₁) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  subst e
  have split : bitArr K j₀ ≫ coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) f = bitArr K' c₀ := by
    rw [Category.assoc]
    congr 1
    apply coprod.hom_ext <;> simp [reassoc_of% h₀]
  have m : coprod.desc (bitArr K j₀) (injArr K j₁ ≫ coprod.inr) ≫
      coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) f =
      coprod.desc (bitArr K' c₀) (injArr K' c₁ ≫ coprod.inr) := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, coprod.inl_desc]
      exact split
    · simp [reassoc_of% h₁]
  exact (congrArg (· ≫ coprod.map (𝟙 _) f) (switchRow_sum K p j₀ j₁)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP p ≫ ·) m).trans (switchRow_sum K' p c₀ c₁).symm))

/-! ## Dispatchers of any rows -/

section Rows

variable {rows : Fin (K + 1) → Region signature.Instr} {rows' : Fin (K' + 1) → Region signature.Instr}
  (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
  (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States K')])

/-- Row squares along a state map give the square of the dispatchers. -/
theorem rows_square (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K'))
    (cls : Fin (K + 1) → Fin (K' + 1)) (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i))
    (row : ∀ i, (ofRegion (h i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion (h' (cls i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (dispatch_typed K h) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      f ≫ (ofRegion (dispatch_typed K' h') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) := by
  apply inj_ext K
  intro i
  exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch K h i) (inj_dispatch K' h' (cls i)) (spec i) (row i)

end Rows

theorem classFold_zero (cls : Fin (K + 1) → Fin 1) :
    classFold (Φ := signature.Instr) State cls = phaseFold State K := by
  apply inj_ext K
  intro i
  exact (class_inj cls i).trans
    ((congrArg (injArr 0) (Fin.eq_zero (cls i))).trans (injArr_base.trans (inj_fold K i).symm))

/-- Uniformity along the class map of a surjection onto any number of states. -/
theorem any_uniform : ∀ {K K' : Nat} {Y : Ty Empty} (cls : Fin (K + 1) → Fin (K' + 1)),
    Function.Surjective cls →
    ∀ (G : ofType (Φ := signature.Instr) (States K) ⟶ ofType Y ⨿ ofType (States K))
      (T : ofType (Φ := signature.Instr) (States K') ⟶ ofType Y ⨿ ofType (States K')),
      G ≫ coprod.map (𝟙 _) (classFold State cls) = classFold State cls ≫ T →
      (π).map (iterate G) = (π).map (classFold State cls ≫ iterate T)
  | K, 0, _, cls, _, G, T, sq => by
    have e := classFold_zero cls
    rw [e] at sq ⊢
    exact fold_uniform false K G T sq
  | _, _ + 1, _, cls, surj, G, T, sq => class_uniform false State cls surj G T sq

section Rows

variable {rows : Fin (K + 1) → Region signature.Instr} {rows' : Fin (K' + 1) → Region signature.Instr}
  (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
  (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States K')])

/-- A surjective class map with row squares identifies the entered loops. -/
theorem dispatch_quotient (cls : Fin (K + 1) → Fin (K' + 1)) (surj : Function.Surjective cls)
    (row : ∀ i, (ofRegion (h i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (classFold State cls) =
      ofRegion (h' (cls i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) (i : Fin (K + 1)) :
    Eqv false [State] (dispatchEntered K rows i) (dispatchEntered K' rows' (cls i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (dispatchEntered_typed h i)
    (dispatchEntered_typed h' (cls i))).1
  change (π).map (ofRegion (dispatchEntered_typed h i)) = (π).map (ofRegion (dispatchEntered_typed h' (cls i)))
  rw [dispatchEntered_arrow h i, dispatchEntered_arrow h' (cls i), dispatchLoop_arrow h, dispatchLoop_arrow h']
  have loops := any_uniform cls surj _ _ (rows_square h h' (classFold State cls) cls (class_inj cls) row)
  have at_i := class_inj cls i
  calc
    _ = (π).map (injArr K i) ≫ (π).map (classFold State cls ≫ iterate _) :=
      ((π).map_comp _ _).trans (congrArg ((π).map (injArr K i) ≫ ·) loops)
    _ = (π).map ((injArr K i ≫ classFold State cls) ≫ iterate _) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = _ := by rw [at_i]

end Rows

/-- Rows at the tail of a larger dispatcher, closed under successors, have
the same entered loops in default Paper. -/
theorem dispatch_tail {P : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    {rows' : Fin (K + (P + 1) + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
    (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States (K + (P + 1)))])
    (row : ∀ j, (ofRegion (h j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (tailArr K P) =
      ofRegion (h' (tailIdx P j)) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + (P + 1)))).hom)
    (j : Fin (K + 1)) :
    ofRegion (dispatchEntered_typed h j) = ofRegion (dispatchEntered_typed h' (tailIdx P j)) := by
  have uni := iterate_uniformity_ofBranchValue (tailTm_typed (K := K) (.var (i := 0) rfl) P) _ _
    (rows_square h h' (tailArr K P) (tailIdx P) (inj_tail P) row)
  rw [dispatchEntered_arrow h j, dispatchEntered_arrow h' (tailIdx P j), dispatchLoop_arrow h,
    dispatchLoop_arrow h']
  exact (congrArg (injArr K j ≫ ·) uni).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Paper.TypeCategory.iterate _) (inj_tail P j)))

/-! ## Switch tables -/

theorem switch_row_map (t : Switch K) (t' : Switch K')
    (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K')) (cls : Fin (K + 1) → Fin (K' + 1))
    (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i)) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i b, cls (t.next i b) = t'.next (cls i) b) (i : Fin (K + 1)) :
    (ofRegion (t.rows_typed i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion (t'.rows_typed (cls i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom :=
  switchRow_class f (t.prog i) (t'.prog (cls i)) (hprog i) _ _ _ _
    ((spec _).trans (congrArg (injArr K') (hnext i false)))
    ((spec _).trans (congrArg (injArr K') (hnext i true)))

theorem switch_quotient_eqv (t : Switch K) (t' : Switch K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i b, cls (t.next i b) = t'.next (cls i) b) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t'.entered (cls i)) [Bit] :=
  dispatch_quotient t.rows_typed t'.rows_typed cls surj
    (switch_row_map t t' (classFold State cls) cls (class_inj cls) hprog hnext) i

theorem switch_tail_arrow {P : Nat} (w : Switch (K + (P + 1))) (s : Switch K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hnext : ∀ j b, tailIdx P (s.next j b) = w.next (tailIdx P j) b) (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) :=
  dispatch_tail s.rows_typed w.rows_typed
    (switch_row_map s w (tailArr K P) (tailIdx P) (inj_tail P) hprog hnext) j

theorem switch_tail_eqv {P : Nat} (w : Switch (K + (P + 1))) (s : Switch K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hnext : ∀ j b, tailIdx P (s.next j b) = w.next (tailIdx P j) b) (j : Fin (K + 1)) :
    Eqv false [State] (s.entered j) (w.entered (tailIdx P j)) [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (s.entered_typed j) (w.entered_typed (tailIdx P j))).1
    (congrArg (π).map (switch_tail_arrow w s hprog hnext j))

section Append

variable {P : Nat} (t : Switch P) (s : Switch K)

theorem switch_prog_front (i : Fin (P + 1)) : (t.append s).prog (frontIdx P i) = t.prog i :=
  joinIdx_front P t.prog s.prog i

theorem switch_prog_tail (j : Fin (K + 1)) : (t.append s).prog (tailIdx P j) = s.prog j :=
  joinIdx_tail P t.prog s.prog j

theorem switch_next_front (i : Fin (P + 1)) (b : Bool) :
    (t.append s).next (frontIdx P i) b = frontIdx P (t.next i b) :=
  congrFun (joinIdx_front (α := Bool → Fin (K + (P + 1) + 1)) P (fun i b => frontIdx P (t.next i b))
    (fun j b => tailIdx P (s.next j b)) i) b

theorem switch_next_tail (j : Fin (K + 1)) (b : Bool) :
    (t.append s).next (tailIdx P j) b = tailIdx P (s.next j b) :=
  congrFun (joinIdx_tail (α := Bool → Fin (K + (P + 1) + 1)) P (fun i b => frontIdx P (t.next i b))
    (fun j b => tailIdx P (s.next j b)) j) b

theorem switch_walk_front : ∀ (w : List Bool) (i : Fin (P + 1)),
    (t.append s).walk (frontIdx P i) w = frontIdx P (t.walk i w)
  | [], _ => rfl
  | b :: w, i => (congrArg ((t.append s).walk · w) (switch_next_front t s i b)).trans
      (switch_walk_front w (t.next i b))

theorem switch_walk_tail : ∀ (w : List Bool) (j : Fin (K + 1)),
    (t.append s).walk (tailIdx P j) w = tailIdx P (s.walk j w)
  | [], _ => rfl
  | b :: w, j => (congrArg ((t.append s).walk · w) (switch_next_tail t s j b)).trans
      (switch_walk_tail w (s.next j b))

end Append

/-- Any map of states that preserves row programs and commutes with both
successors identifies the entered loops. -/
theorem switch_morphism_eqv {P : Nat} (s : Switch K) (t : Switch P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hnext : ∀ j b, ρ (s.next j b) = t.next (ρ j) b)
    (j : Fin (K + 1)) : Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] := by
  have tail := switch_tail_eqv (t.append s) s (fun j => (switch_prog_tail t s j).symm)
    (fun j b => (switch_next_tail t s j b).symm) j
  have cprog : ∀ x, (t.append s).prog x = t.prog (joinIdx P id ρ x) := by
    intro x
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (switch_prog_front t s i).trans (congrArg t.prog (joinIdx_front P id ρ i)).symm
    · exact (switch_prog_tail t s j).trans ((hprog j).trans (congrArg t.prog (joinIdx_tail P id ρ j)).symm)
  have cnext : ∀ x b, joinIdx P id ρ ((t.append s).next x b) = t.next (joinIdx P id ρ x) b := by
    intro x b
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (congrArg (joinIdx P id ρ) (switch_next_front t s i b)).trans
        ((joinIdx_front P id ρ (t.next i b)).trans (congrArg (t.next · b) (joinIdx_front P id ρ i)).symm)
    · exact (congrArg (joinIdx P id ρ) (switch_next_tail t s j b)).trans
        ((joinIdx_tail P id ρ (s.next j b)).trans
          ((hnext j b).trans (congrArg (t.next · b) (joinIdx_tail P id ρ j)).symm))
  have quot := switch_quotient_eqv (t.append s) t (joinIdx P id ρ)
    (fun i => ⟨frontIdx P i, joinIdx_front P id ρ i⟩) cprog cnext (tailIdx P j)
  exact tail.trans (joinIdx_tail P id ρ j ▸ quot)

theorem switch_rep_tree (t : Switch K) (x : Fin (K + 1)) (w : List Bool) :
    t.prog (t.walk (t.rep x) w) = t.prog (t.walk x w) := by
  have h : t.treeSetoid.r (t.rep x) x := Quotient.exact (Quotient.out_eq (Quotient.mk t.treeSetoid x))
  exact h w

theorem switch_rep_congr (t : Switch K) {x y : Fin (K + 1)}
    (h : ∀ w, t.prog (t.walk x w) = t.prog (t.walk y w)) : t.rep x = t.rep y :=
  congrArg Quotient.out (Quotient.sound (s := t.treeSetoid) h)

/-- Two states of one table that run the same programs along every word. -/
theorem switch_tree_eqv (t : Switch K) (x y : Fin (K + 1))
    (h : ∀ w, t.prog (t.walk x w) = t.prog (t.walk y w)) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] := by
  have hp : ∀ x, t.prog x = t.minimized.prog (t.rep x) := fun x => (switch_rep_tree t x []).symm
  have hn : ∀ x b, t.rep (t.next x b) = t.minimized.next (t.rep x) b :=
    fun x b => switch_rep_congr t (fun w => (switch_rep_tree t x (b :: w)).symm)
  exact (switch_morphism_eqv t t.minimized t.rep hp hn x).trans
    (switch_rep_congr t h ▸ (switch_morphism_eqv t t.minimized t.rep hp hn y).symm)

/-- Entries of two tables that run the same programs along every word. -/
theorem switch_bisim_eqv {K₁ K₂ : Nat} (t₁ : Switch K₁) (t₂ : Switch K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) (h : ∀ w, t₁.prog (t₁.walk i₁ w) = t₂.prog (t₂.walk i₂ w)) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] := by
  have e₁ := switch_tail_eqv (t₂.append t₁) t₁ (fun j => (switch_prog_tail t₂ t₁ j).symm)
    (fun j b => (switch_next_tail t₂ t₁ j b).symm) i₁
  have e₂ := switch_morphism_eqv t₂ (t₂.append t₁) (frontIdx K₂) (fun i => (switch_prog_front t₂ t₁ i).symm)
    (fun i b => (switch_next_front t₂ t₁ i b).symm) i₂
  have tail : ∀ w, (t₂.append t₁).prog ((t₂.append t₁).walk (tailIdx K₂ i₁) w) = t₁.prog (t₁.walk i₁ w) :=
    fun w => (congrArg (t₂.append t₁).prog (switch_walk_tail t₂ t₁ w i₁)).trans (switch_prog_tail t₂ t₁ _)
  have front : ∀ w, (t₂.append t₁).prog ((t₂.append t₁).walk (frontIdx K₂ i₂) w) = t₂.prog (t₂.walk i₂ w) :=
    fun w => (congrArg (t₂.append t₁).prog (switch_walk_front t₂ t₁ w i₂)).trans (switch_prog_front t₂ t₁ _)
  exact e₁.trans ((switch_tree_eqv (t₂.append t₁) _ _
    (fun w => (tail w).trans ((h w).trans (front w).symm))).trans e₂.symm)

theorem walk_rel {K₁ K₂ : Nat} (t₁ : Switch K₁) (t₂ : Switch K₂) (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (next : ∀ x y, R x y → ∀ b, R (t₁.next x b) (t₂.next y b)) :
    ∀ (w : List Bool) (x : Fin (K₁ + 1)) (y : Fin (K₂ + 1)), R x y → R (t₁.walk x w) (t₂.walk y w)
  | [], _, _, r => r
  | b :: w, x, y, r => walk_rel t₁ t₂ R next w _ _ (next x y r b)

/-- Replay from a bisimulation. -/
theorem switch_bisimulation_eqv {K₁ K₂ : Nat} (t₁ : Switch K₁) (t₂ : Switch K₂)
    (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) (bis : Switch.Bisimulation t₁ t₂ R) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) (r : R i₁ i₂) : Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  switch_bisim_eqv t₁ t₂ i₁ i₂ (fun w => bis.prog _ _ (walk_rel t₁ t₂ R bis.next w i₁ i₂ r))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
