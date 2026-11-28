module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SwitchTables

/-! # Replay for tables with arbitrary routing of the packed result -/

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

/-! ## Squares of case splits, sequencing and leaves -/

section Squares

variable {K K' : Nat} (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K'))

theorem case_nat {A B : Ty Empty} {r s r' s' : Region signature.Instr}
    (ha : ValueBranches [A] r [Silmaril.coprod Bit (States K)])
    (hb : ValueBranches [B] s [Silmaril.coprod Bit (States K)])
    (ha' : ValueBranches [A] r' [Silmaril.coprod Bit (States K')])
    (hb' : ValueBranches [B] s' [Silmaril.coprod Bit (States K')])
    (na : (ofRegion ha ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion ha' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom)
    (nb : (ofRegion hb ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion hb' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (caseValueBranches ha hb) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (caseValueBranches ha' hb') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  rw [← coprod_desc_ofRegion ha hb, ← coprod_desc_ofRegion ha' hb']
  simp only [Category.assoc]
  congr 1
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc]
    exact (Category.assoc _ _ _).symm.trans na
  · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc]
    exact (Category.assoc _ _ _).symm.trans nb

theorem seq_nat (p : Program) {r r' : Region signature.Instr}
    (hr : ValueBranches [Silmaril.coprod Bit State] r [Silmaril.coprod Bit (States K)])
    (hr' : ValueBranches [Silmaril.coprod Bit State] r' [Silmaril.coprod Bit (States K')])
    (n : (ofRegion hr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion hr' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (seqValueBranches (step_typed p) hr) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (seqValueBranches (step_typed p) hr') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  rw [← Paper.TypeCategory.ofRegion_comp (step_typed p) hr (seqValueBranches (step_typed p) hr),
    ← Paper.TypeCategory.ofRegion_comp (step_typed p) hr' (seqValueBranches (step_typed p) hr')]
  simp only [Category.assoc]
  exact congrArg (ofRegion (step_typed p) ≫ ·) ((Category.assoc _ _ _).symm.trans n)

theorem dead_nat :
    (ofRegion (dead_typed K) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion (dead_typed K') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  have e : ofRegion (dead_typed K) =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  have e' : ofRegion (dead_typed K') =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K')).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  rw [e, e']
  simp

theorem act_nat (cls : Fin (K + 1) → Fin (K' + 1)) (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i))
    (a : Act K) :
    (ofRegion (act_typed K a) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion (act_typed K' (a.map cls)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  cases a with
  | ret c =>
    have e : ofRegion (act_typed K (.ret c)) =
        ofRegion (r := .br 0 (bitTm c)) (.br rfl (bitTm_typed c)) ≫
          (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
      br_inl (bitTm_typed c)
    have e' : ofRegion (act_typed K' ((Act.ret c : Act K).map cls)) =
        ofRegion (r := .br 0 (bitTm c)) (.br rfl (bitTm_typed c)) ≫
          (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K')).inv) :=
      br_inl (bitTm_typed c)
    rw [e, e']
    simp
  | go j q =>
    have e : ofRegion (act_typed K (.go j q)) =
        (ofRegion (r := .br 0 (.inl (bitTm q))) (.br (L := [State]) rfl (.inl (bitTm_typed q))) ≫ injArr K j) ≫
          (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
      (br_inr (injTm_typed (.inl (bitTm_typed q)) K j)).trans
        (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv))
          (injOf_eq (.inl (bitTm_typed q)) K j))
    have e' : ofRegion (act_typed K' ((Act.go j q : Act K).map cls)) =
        (ofRegion (r := .br 0 (.inl (bitTm q))) (.br (L := [State]) rfl (.inl (bitTm_typed q))) ≫
            injArr K' (cls j)) ≫
          (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K')).inv) :=
      (br_inr (injTm_typed (.inl (bitTm_typed q)) K' (cls j))).trans
        (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K')).inv))
          (injOf_eq (.inl (bitTm_typed q)) K' (cls j)))
    rw [e, e']
    simp [reassoc_of% spec j]

/-- A router row commutes with a state map that renames its targets. -/
theorem routerRow_nat (cls : Fin (K + 1) → Fin (K' + 1)) (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i))
    (p p' : Program) (ep : p = p') (a : Bool → Bool → Act K) (a' : Bool → Bool → Act K')
    (ea : ∀ x b, a' x b = (a x b).map cls) :
    (ofRegion (routerRow_typed K p a) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (routerRow_typed K' p' a') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  subst ep
  have ea' : a' = fun x b => (a x b).map cls := funext fun x => funext fun b => ea x b
  subst ea'
  exact seq_nat f p _ _
    (case_nat f _ _ _ _ (case_nat f _ _ _ _ (act_nat f cls spec _) (act_nat f cls spec _))
      (case_nat f _ _ _ _ (case_nat f _ _ _ _ (act_nat f cls spec _) (act_nat f cls spec _)) (dead_nat f)))

end Squares

/-! ## Actions -/

section Actions

variable {K₁ K₂ K₃ : Nat}

theorem Act.map_map_of {g : Fin (K₂ + 1) → Fin (K₃ + 1)} {h : Fin (K₁ + 1) → Fin (K₂ + 1)}
    {k : Fin (K₁ + 1) → Fin (K₃ + 1)} (e : ∀ i, g (h i) = k i) (a : Act K₁) : (a.map h).map g = a.map k := by
  cases a with
  | ret c => rfl
  | go j q => exact congrArg (Act.go · q) (e j)

theorem Act.map_cancel {g : Fin (K₂ + 1) → Fin (K₁ + 1)} {h : Fin (K₁ + 1) → Fin (K₂ + 1)}
    (e : ∀ i, g (h i) = i) (a : Act K₁) : (a.map h).map g = a := by
  cases a with
  | ret c => rfl
  | go j q => exact congrArg (Act.go · q) (e j)

theorem rel_refl (a : Act K₁) : Act.Rel (fun x y => x = y) a a := by
  cases a with
  | ret c => exact rfl
  | go j q => exact ⟨rfl, rfl⟩

theorem rel_symm {R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop} {a : Act K₁} {a' : Act K₂} (h : Act.Rel R a a') :
    Act.Rel (fun y x => R x y) a' a := by
  cases a <;> cases a' <;> first | exact h.elim | exact h.symm | exact ⟨h.1.symm, h.2⟩

theorem rel_trans {R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop} {R' : Fin (K₂ + 1) → Fin (K₃ + 1) → Prop}
    {a : Act K₁} {b : Act K₂} {c : Act K₃} (h : Act.Rel R a b) (h' : Act.Rel R' b c) :
    Act.Rel (fun x z => ∃ y, R x y ∧ R' y z) a c := by
  cases a <;> cases b <;> cases c <;>
    first | exact h.elim | exact h'.elim | exact h.trans h' | exact ⟨h.1.trans h'.1, _, h.2, h'.2⟩

theorem rel_map {K₄ : Nat} {R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop} {S : Fin (K₃ + 1) → Fin (K₄ + 1) → Prop}
    {g : Fin (K₁ + 1) → Fin (K₃ + 1)} {g' : Fin (K₂ + 1) → Fin (K₄ + 1)}
    (hs : ∀ j j', R j j' → S (g j) (g' j')) {a : Act K₁} {a' : Act K₂} (h : Act.Rel R a a') :
    Act.Rel S (a.map g) (a'.map g') := by
  cases a <;> cases a' <;> first | exact h.elim | exact ⟨h.1, hs _ _ h.2⟩ | exact h

theorem rel_map_eq {R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop} {g : Fin (K₁ + 1) → Fin (K₃ + 1)}
    {g' : Fin (K₂ + 1) → Fin (K₃ + 1)} (hs : ∀ j j', R j j' → g j = g' j') {a : Act K₁} {a' : Act K₂}
    (h : Act.Rel R a a') : a.map g = a'.map g' := by
  cases a with
  | ret c =>
    cases a' with
    | ret c' => exact congrArg Act.ret h
    | go j' q' => exact h.elim
  | go j q =>
    cases a' with
    | ret c' => exact h.elim
    | go j' q' =>
      obtain ⟨rfl, r⟩ := h
      exact congrArg (Act.go · q) (hs _ _ r)

end Actions

/-! ## Router tables -/

variable {K K' : Nat}

theorem router_row_map (s : Router K) (t : Router K')
    (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K')) (cls : Fin (K + 1) → Fin (K' + 1))
    (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i)) (hprog : ∀ i, s.prog i = t.prog (cls i))
    (hact : ∀ i x b, t.act (cls i) x b = (s.act i x b).map cls) (i : Fin (K + 1)) :
    (ofRegion (s.rows_typed i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      ofRegion (t.rows_typed (cls i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom :=
  routerRow_nat f cls spec (s.prog i) (t.prog (cls i)) (hprog i) (s.act i) (t.act (cls i)) (hact i)

theorem router_quotient_eqv (s : Router K) (t : Router K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, s.prog i = t.prog (cls i))
    (hact : ∀ i x b, t.act (cls i) x b = (s.act i x b).map cls) (i : Fin (K + 1)) :
    Eqv false [State] (s.entered i) (t.entered (cls i)) [Bit] :=
  dispatch_quotient s.rows_typed t.rows_typed cls surj
    (router_row_map s t (classFold State cls) cls (class_inj cls) hprog hact) i

theorem router_tail_arrow {P : Nat} (w : Router (K + (P + 1))) (s : Router K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hact : ∀ j x b, w.act (tailIdx P j) x b = (s.act j x b).map (tailIdx P)) (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) :=
  dispatch_tail s.rows_typed w.rows_typed
    (router_row_map s w (tailArr K P) (tailIdx P) (inj_tail P) hprog hact) j

theorem router_tail_eqv {P : Nat} (w : Router (K + (P + 1))) (s : Router K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hact : ∀ j x b, w.act (tailIdx P j) x b = (s.act j x b).map (tailIdx P)) (j : Fin (K + 1)) :
    Eqv false [State] (s.entered j) (w.entered (tailIdx P j)) [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (s.entered_typed j) (w.entered_typed (tailIdx P j))).1
    (congrArg (π).map (router_tail_arrow w s hprog hact j))

section Append

variable {P : Nat} (t : Router P) (s : Router K)

theorem router_prog_front (i : Fin (P + 1)) : (t.append s).prog (frontIdx P i) = t.prog i :=
  joinIdx_front P t.prog s.prog i

theorem router_prog_tail (j : Fin (K + 1)) : (t.append s).prog (tailIdx P j) = s.prog j :=
  joinIdx_tail P t.prog s.prog j

theorem router_act_front (i : Fin (P + 1)) (x b : Bool) :
    (t.append s).act (frontIdx P i) x b = (t.act i x b).map (frontIdx P) :=
  congrFun (congrFun (joinIdx_front (α := Bool → Bool → Act (K + (P + 1))) P
    (fun i x b => (t.act i x b).map (frontIdx P)) (fun j x b => (s.act j x b).map (tailIdx P)) i) x) b

theorem router_act_tail (j : Fin (K + 1)) (x b : Bool) :
    (t.append s).act (tailIdx P j) x b = (s.act j x b).map (tailIdx P) :=
  congrFun (congrFun (joinIdx_tail (α := Bool → Bool → Act (K + (P + 1))) P
    (fun i x b => (t.act i x b).map (frontIdx P)) (fun j x b => (s.act j x b).map (tailIdx P)) j) x) b

end Append

/-- Any map of states that preserves row programs and renames the targets
of all four actions identifies the entered loops. -/
theorem router_morphism_eqv {P : Nat} (s : Router K) (t : Router P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hact : ∀ j x b, t.act (ρ j) x b = (s.act j x b).map ρ)
    (j : Fin (K + 1)) : Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] := by
  have tail := router_tail_eqv (t.append s) s (fun j => (router_prog_tail t s j).symm)
    (router_act_tail t s) j
  have cprog : ∀ x, (t.append s).prog x = t.prog (joinIdx P id ρ x) := by
    intro x
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (router_prog_front t s i).trans (congrArg t.prog (joinIdx_front P id ρ i)).symm
    · exact (router_prog_tail t s j).trans ((hprog j).trans (congrArg t.prog (joinIdx_tail P id ρ j)).symm)
  have cact : ∀ x a b, t.act (joinIdx P id ρ x) a b = ((t.append s).act x a b).map (joinIdx P id ρ) := by
    intro x a b
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [router_act_front, Act.map_cancel (joinIdx_front P id ρ)]
      exact congrArg (t.act · a b) (joinIdx_front P id ρ i)
    · rw [router_act_tail, Act.map_map_of (joinIdx_tail P id ρ)]
      exact (congrArg (t.act · a b) (joinIdx_tail P id ρ j)).trans (hact j a b)
  have quot := router_quotient_eqv (t.append s) t (joinIdx P id ρ)
    (fun i => ⟨frontIdx P i, joinIdx_front P id ρ i⟩) cprog cact (tailIdx P j)
  exact tail.trans (joinIdx_tail P id ρ j ▸ quot)

/-! ## Bisimilar states -/

theorem bisimilar_refl (t : Router K) (x : Fin (K + 1)) : t.Bisimilar t x x :=
  ⟨fun x y => x = y, ⟨fun _ _ e => e ▸ rfl, fun _ _ e _ _ => e ▸ rel_refl _⟩, rfl⟩

theorem bisimilar_symm (t : Router K) {x y : Fin (K + 1)} : t.Bisimilar t x y → t.Bisimilar t y x :=
  fun ⟨R, bis, r⟩ => ⟨fun y x => R x y,
    ⟨fun y x r => (bis.prog x y r).symm, fun y x r a b => rel_symm (bis.act x y r a b)⟩, r⟩

theorem bisimilar_trans (t : Router K) {x y z : Fin (K + 1)} :
    t.Bisimilar t x y → t.Bisimilar t y z → t.Bisimilar t x z :=
  fun ⟨R, bis, r⟩ ⟨R', bis', r'⟩ => ⟨fun x z => ∃ y, R x y ∧ R' y z,
    ⟨fun x z ⟨y, a, b⟩ => (bis.prog x y a).trans (bis'.prog y z b),
      fun x z ⟨y, a, b⟩ c d => rel_trans (bis.act x y a c d) (bis'.act y z b c d)⟩, ⟨y, r, r'⟩⟩

@[expose] def bisimSetoid (t : Router K) : Setoid (Fin (K + 1)) :=
  ⟨t.Bisimilar t, ⟨bisimilar_refl t, bisimilar_symm t, bisimilar_trans t⟩⟩

/-- A chosen bisimilar state. Bisimilar states get the same one. -/
@[expose] noncomputable def routerRep (t : Router K) (x : Fin (K + 1)) : Fin (K + 1) :=
  (Quotient.mk (bisimSetoid t) x).out

/-- The same rows, with every target replaced by its representative. -/
@[expose] noncomputable def routerMin (t : Router K) : Router K :=
  ⟨t.prog, fun x a b => (t.act x a b).map (routerRep t)⟩

theorem rep_bisimilar (t : Router K) (x : Fin (K + 1)) : t.Bisimilar t (routerRep t x) x :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (bisimSetoid t) x))

theorem rep_eq (t : Router K) {x y : Fin (K + 1)} (h : t.Bisimilar t x y) : routerRep t x = routerRep t y :=
  congrArg Quotient.out (Quotient.sound (s := bisimSetoid t) h)

/-- Bisimilar states of one table have equal entered loops. -/
theorem router_self_eqv (t : Router K) (x y : Fin (K + 1)) (h : t.Bisimilar t x y) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] := by
  have hp : ∀ x, t.prog x = (routerMin t).prog (routerRep t x) := by
    intro x
    obtain ⟨R, bis, r⟩ := rep_bisimilar t x
    exact (bis.prog _ _ r).symm
  have ha : ∀ x a b, (routerMin t).act (routerRep t x) a b = (t.act x a b).map (routerRep t) := by
    intro x a b
    obtain ⟨R, bis, r⟩ := rep_bisimilar t x
    exact rel_map_eq (fun j j' rj => rep_eq t ⟨R, bis, rj⟩) (bis.act _ _ r a b)
  exact (router_morphism_eqv t (routerMin t) (routerRep t) hp ha x).trans
    (rep_eq t h ▸ (router_morphism_eqv t (routerMin t) (routerRep t) hp ha y).symm)

/-- Replay from a bisimulation between two tables. -/
theorem router_bisimulation_eqv {K₁ K₂ : Nat} (t₁ : Router K₁) (t₂ : Router K₂)
    (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) (bis : Router.Bisimulation t₁ t₂ R) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) (r : R i₁ i₂) : Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] := by
  have e₁ := router_tail_eqv (t₂.append t₁) t₁ (fun j => (router_prog_tail t₂ t₁ j).symm)
    (router_act_tail t₂ t₁) i₁
  have e₂ := router_morphism_eqv t₂ (t₂.append t₁) (frontIdx K₂) (fun i => (router_prog_front t₂ t₁ i).symm)
    (router_act_front t₂ t₁) i₂
  have mid : (t₂.append t₁).Bisimilar (t₂.append t₁) (tailIdx K₂ i₁) (frontIdx K₂ i₂) := by
    refine ⟨fun u v => ∃ x y, u = tailIdx K₂ x ∧ v = frontIdx K₂ y ∧ R x y, ⟨?_, ?_⟩, ⟨i₁, i₂, rfl, rfl, r⟩⟩
    · rintro _ _ ⟨x, y, rfl, rfl, rxy⟩
      exact (router_prog_tail t₂ t₁ x).trans ((bis.prog x y rxy).trans (router_prog_front t₂ t₁ y).symm)
    · rintro _ _ ⟨x, y, rfl, rfl, rxy⟩ a b
      rw [router_act_tail, router_act_front]
      exact rel_map (fun j j' rj => ⟨j, j', rfl, rfl, rj⟩) (bis.act x y rxy a b)
  exact e₁.trans ((router_self_eqv (t₂.append t₁) _ _ mid).trans e₂.symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
