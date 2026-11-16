module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Defs
public import Silmaril.Logic.Consequence.Gentzen.Calculus.Thms
public import Silmaril.Logic.Consequence.Gentzen.Translate.Thms
public import Silmaril.Logic.Consequence.Gentzen.Core.Thms
public import Silmaril.Logic.Consequence.Signed.Thms

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Clausal.Thms`. -/

@[expose] public section

set_option linter.unusedSimpArgs false

/-- Close a membership-inclusion goal between concatenations of lists. -/
macro "mem_tac" : tactic => `(tactic| (intro x hx; simp only [List.append_eq, List.map_append,
  List.map_cons, List.cons_append, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
  List.not_mem_nil, or_false] at hx ⊢; tauto))

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal

open Silmaril.Consequence Silmaril.Consequence.Gentzen Silmaril.Consequence.Gentzen.Clausal

universe u v

variable {C : Type u} {neg : C → C}

/-- A two-element list is included in any list containing both members. -/
theorem pair_subset {x y : C} {l : List C} (hx : x ∈ l) (hy : y ∈ l) : [x, y] ⊆ l := by
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

/-! ## UNSAT acceptors and Gentzen calculi -/

section Unsat

variable {S : Seq C} {U : List C → Prop}

theorem unsatClosed_toUnsat (h : GentzenClosed neg S) : UnsatClosed neg (toUnsat S) := by
  obtain ⟨hS, hL, hR⟩ := h
  refine ⟨fun l l' hl hd => hS.weak hl (fun _ hx => hx) hd, ?_, ?_⟩
  · intro Γ c hc hn
    have h0 : S [c] [c] := hS.refl trivial (List.mem_singleton_self c) (List.mem_singleton_self c)
    have h1 : S [neg c, c] [] := hL h0
    exact hS.weak (pair_subset hn hc) (fun _ hx => hx) h1
  · intro a Γ Γ' h₁ h₂
    have h₃ : S Γ [a] := negL_inv hS hR h₁
    exact hS.cut trivial h₃ h₂

/-- Double negation is absorbed by explosion and cut. -/
theorem unsatClosed_dne (h : UnsatClosed neg U) {g : C} {X : List C} (hg : U (g :: X)) :
    U (neg (neg g) :: X) := by
  have h0 : U (neg g :: [neg (neg g)]) :=
    h.explode (c := neg g) (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self)
  have h1 := h.cut h0 hg
  exact h.up _ _ (by mem_tac) h1

theorem gentzenClosed_viaUnsat (h : UnsatClosed neg U) : GentzenClosed neg (viaUnsat U neg) := by
  refine ⟨⟨fun _ Γ Δ c hΓ hΔ => ?_, fun Γ Γ' Δ Δ' h₁ h₂ hd => ?_, fun _ Γ Γ' Δ Δ' a h₁ h₂ => ?_⟩,
    fun Γ Δ d hd => ?_, fun Γ Δ g hg => ?_⟩
  · exact h.explode (c := c) (List.mem_append_left _ hΓ)
      (List.mem_append_right _ (List.mem_map_of_mem hΔ))
  · exact h.up _ _ (List.append_subset.2 ⟨fun _ hx => List.mem_append_left _ (h₁ hx),
      fun _ hx => List.mem_append_right _ (List.map_subset neg h₂ hx)⟩) hd
  · change U (Γ ++ (a :: Δ).map neg) at h₁
    change U ((a :: Γ') ++ Δ'.map neg) at h₂
    change U ((Γ ++ Γ') ++ (Δ ++ Δ').map neg)
    have h₁' : U (neg a :: (Γ ++ Δ.map neg)) := h.up _ _ (by mem_tac) h₁
    have h₃ := h.cut h₁' h₂
    exact h.up _ _ (by mem_tac) h₃
  · change U (Γ ++ (d :: Δ).map neg) at hd
    change U ((neg d :: Γ) ++ Δ.map neg)
    exact h.up _ _ (by mem_tac) hd
  · change U ((g :: Γ) ++ Δ.map neg) at hg
    change U (Γ ++ (neg g :: Δ).map neg)
    have := unsatClosed_dne h (X := Γ ++ Δ.map neg) hg
    exact h.up _ _ (by mem_tac) this

end Unsat

/-! ## TAUTO acceptors and Gentzen calculi -/

section Taut

variable {S : Seq C} {T : List C → Prop}

theorem tautClosed_toTaut (h : GentzenClosed neg S) : TautClosed neg (toTaut S) := by
  obtain ⟨hS, hL, hR⟩ := h
  refine ⟨fun l l' hl hd => hS.weak (fun _ hx => hx) hl hd, ?_, ?_⟩
  · intro Δ c hc hn
    have h0 : S [c] [c] := hS.refl trivial (List.mem_singleton_self c) (List.mem_singleton_self c)
    have h1 : S [] [neg c, c] := hR h0
    exact hS.weak (fun _ hx => hx) (pair_subset hn hc) h1
  · intro a Δ Δ' h₁ h₂
    have h₃ : S [a] Δ' := negR_inv hS hL h₂
    exact hS.cut trivial h₁ h₃

/-- Double negation is absorbed by excluded middle and cut. -/
theorem tautClosed_dni (h : TautClosed neg T) {d : C} {X : List C} (hd : T (d :: X)) :
    T (neg (neg d) :: X) := by
  have h0 : T (neg d :: [neg (neg d)]) :=
    h.excluded (c := neg d) (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self)
  have h1 := h.cut hd h0
  exact h.up _ _ (by mem_tac) h1

theorem gentzenClosed_viaTauto (h : TautClosed neg T) : GentzenClosed neg (viaTauto T neg) := by
  refine ⟨⟨fun _ Γ Δ c hΓ hΔ => ?_, fun Γ Γ' Δ Δ' h₁ h₂ hd => ?_, fun _ Γ Γ' Δ Δ' a h₁ h₂ => ?_⟩,
    fun Γ Δ d hd => ?_, fun Γ Δ g hg => ?_⟩
  · exact h.excluded (c := c) (List.mem_append_right _ hΔ)
      (List.mem_append_left _ (List.mem_map_of_mem hΓ))
  · exact h.up _ _ (List.append_subset.2 ⟨fun _ hx => List.mem_append_left _
      (List.map_subset neg h₁ hx), fun _ hx => List.mem_append_right _ (h₂ hx)⟩) hd
  · change T (Γ.map neg ++ a :: Δ) at h₁
    change T ((a :: Γ').map neg ++ Δ') at h₂
    change T ((Γ ++ Γ').map neg ++ (Δ ++ Δ'))
    have h₁' : T (a :: (Γ.map neg ++ Δ)) := h.up _ _ (by mem_tac) h₁
    have h₃ := h.cut h₁' h₂
    exact h.up _ _ (by mem_tac) h₃
  · change T (Γ.map neg ++ d :: Δ) at hd
    change T ((neg d :: Γ).map neg ++ Δ)
    have h₁ : T (d :: (Γ.map neg ++ Δ)) := h.up _ _ (by mem_tac) hd
    exact h.up _ _ (by mem_tac) (tautClosed_dni h h₁)
  · change T ((g :: Γ).map neg ++ Δ) at hg
    change T (Γ.map neg ++ neg g :: Δ)
    exact h.up _ _ (by mem_tac) hg

end Taut

/-! ## CNF acceptors and their unit restrictions -/

section Cnf

variable {A : List (List C) → Prop} {U : List C → Prop}

theorem units_cons (c : C) (Γ : List C) : units (c :: Γ) = [c] :: units Γ := rfl

theorem units_append (Γ Γ' : List C) : units (Γ ++ Γ') = units Γ ++ units Γ' := List.map_append

theorem mem_units {K : List C} {Γ : List C} : K ∈ units Γ ↔ ∃ c ∈ Γ, [c] = K := by
  simp [units]

theorem hits_units {Γ Γ' : List C} : Hits Γ' (units Γ) ↔ Γ ⊆ Γ' := by
  constructor
  · intro h c hc
    obtain ⟨d, hd, hd'⟩ := h [c] (mem_units.2 ⟨c, hc, rfl⟩)
    rw [List.mem_singleton] at hd
    exact hd ▸ hd'
  · intro h K hK
    obtain ⟨c, hc, rfl⟩ := mem_units.1 hK
    exact ⟨c, List.mem_singleton_self c, h hc⟩

theorem units_subset {Γ Γ' : List C} (h : Γ ⊆ Γ') : units Γ ⊆ units Γ' := List.map_subset _ h

theorem hits_mono {Γ : List C} {F G : List (List C)} (h : F ⊆ G) (hG : Hits Γ G) : Hits Γ F :=
  fun K hK => hG K (h hK)

theorem unitsOf_up (hA : CnfClosed A) : ListPred.UpClosed (unitsOf A) :=
  fun _ _ h hd => hA.up _ _ (units_subset h) hd

theorem unitsOf_cnfOf (hU : ListPred.UpClosed U) : unitsOf (cnfOf U) = U := by
  funext Γ
  apply propext
  constructor
  · intro h; exact h Γ (hits_units.2 (fun _ hx => hx))
  · intro h Γ' hΓ'; exact hU _ _ (hits_units.1 hΓ') h

theorem cnfClosed_cnfOf (U : List C → Prop) : CnfClosed (cnfOf U) := by
  refine ⟨fun F G h hF Γ hΓ => hF Γ (hits_mono h hΓ), ?_, ?_, ?_⟩
  · intro K K' F hK h Γ hΓ
    refine h Γ fun L hL => ?_
    rcases List.mem_cons.1 hL with rfl | hL
    · obtain ⟨c, hc, hcΓ⟩ := hΓ K' List.mem_cons_self
      exact ⟨c, hK hc, hcΓ⟩
    · exact hΓ L (List.mem_cons_of_mem _ hL)
  · intro a K F h₁ h₂ Γ hΓ
    obtain ⟨c, hc, hcΓ⟩ := hΓ _ List.mem_cons_self
    have hF : Hits Γ F := fun L hL => hΓ L (List.mem_cons_of_mem _ hL)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h₁ Γ fun L hL => by
        rcases List.mem_cons.1 hL with rfl | hL
        · exact ⟨c, List.mem_singleton_self c, hcΓ⟩
        · exact hF L hL
    · exact h₂ Γ fun L hL => by
        rcases List.mem_cons.1 hL with rfl | hL
        · exact ⟨c, hc, hcΓ⟩
        · exact hF L hL
  · intro F Γ hΓ
    obtain ⟨_, hc, _⟩ := hΓ [] List.mem_cons_self
    exact absurd hc List.not_mem_nil

/-- An accepted formula has its hitting lists' units accepted, beside any extra clauses. -/
theorem units_of_accept (hA : CnfClosed A) {Γ : List C} :
    ∀ (F X : List (List C)), Hits Γ F → A (F ++ X) → A (X ++ units Γ)
  | [], X, _, h => hA.up _ _ (fun x hx => List.mem_append_left _ hx) h
  | K :: F, X, hΓ, h => by
    obtain ⟨c, hc, hcΓ⟩ := hΓ K List.mem_cons_self
    have h₁ : A ([c] :: (F ++ X)) := hA.strengthen ((by intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hc)) h
    have h₂ : A (F ++ (X ++ [[c]])) := hA.up _ _ (by mem_tac) h₁
    have h₃ := units_of_accept hA F (X ++ [[c]]) (fun L hL => hΓ L (List.mem_cons_of_mem _ hL)) h₂
    have hcu : [c] ∈ units Γ := mem_units.2 ⟨c, hcΓ, rfl⟩
    exact hA.up _ _ (fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hx ⊢
      rcases hx with (hx | rfl | hx) | hx
      · exact Or.inl hx
      · exact Or.inr hcu
      · exact hx.elim
      · exact Or.inr hx) h₃

/-- Splitting a clause into its literals. -/
theorem accept_of_literals (hA : CnfClosed A) {F : List (List C)} :
    ∀ K : List C, (∀ a ∈ K, A ([a] :: F)) → A (K :: F)
  | [], _ => hA.empty F
  | a :: K, h => hA.split (h a List.mem_cons_self)
      (accept_of_literals hA K fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem accept_of_units (hA : CnfClosed A) :
    ∀ (F G : List (List C)), (∀ Γ, Hits Γ F → A (G ++ units Γ)) → A (G ++ F)
  | [], G, h => by simpa [units] using h [] (fun _ hK => absurd hK List.not_mem_nil)
  | K :: F, G, h => by
    have hlit : ∀ a ∈ K, A ([a] :: (G ++ F)) := by
      intro a ha
      have := accept_of_units hA F (G ++ [[a]]) fun Γ hΓ => by
        have h₁ := h (a :: Γ) fun L hL => by
          rcases List.mem_cons.1 hL with rfl | hL
          · exact ⟨a, ha, List.mem_cons_self⟩
          · obtain ⟨c, hc, hcΓ⟩ := hΓ L hL
            exact ⟨c, hc, List.mem_cons_of_mem _ hcΓ⟩
        rw [units_cons] at h₁
        exact hA.up _ _ (by mem_tac) h₁
      exact hA.up _ _ (by mem_tac) this
    have := accept_of_literals hA K hlit
    exact hA.up _ _ (by mem_tac) this

theorem cnfOf_unitsOf (hA : CnfClosed A) : cnfOf (unitsOf A) = A := by
  funext F
  apply propext
  constructor
  · intro h
    simpa using accept_of_units hA F [] fun Γ hΓ => by simpa [unitsOf] using h Γ hΓ
  · intro h Γ hΓ
    simpa [unitsOf] using units_of_accept hA F [] hΓ (by simpa using h)

theorem cnfUnsatClosed_iff : CnfUnsatClosed neg A ↔ CnfClosed A ∧ UnsatClosed neg (unitsOf A) := by
  constructor
  · intro h
    refine ⟨h.toCnfClosed, unitsOf_up h.toCnfClosed, fun Γ c hc hn => ?_, fun a Γ Γ' h₁ h₂ => ?_⟩
    · exact h.up _ _ (fun K hK => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
        rcases hK with rfl | rfl
        · exact mem_units.2 ⟨c, hc, rfl⟩
        · exact mem_units.2 ⟨neg c, hn, rfl⟩) (h.complement c)
    · have := h.unitCut (F := units Γ) (G := units Γ') h₁ h₂
      unfold unitsOf; rwa [units_append]
  · rintro ⟨hA, hU⟩
    refine ⟨hA, fun c => hU.explode (Γ := [c, neg c]) (c := c) List.mem_cons_self
      (List.mem_cons_of_mem _ List.mem_cons_self), fun a F G h₁ h₂ => ?_⟩
    rw [← cnfOf_unitsOf hA] at h₁ h₂ ⊢
    intro Γ hΓ
    have hF : Hits Γ F := hits_mono (fun _ hx => List.mem_append_left _ hx) hΓ
    have hG : Hits Γ G := hits_mono (fun _ hx => List.mem_append_right _ hx) hΓ
    have k₁ := h₁ (neg a :: Γ) fun L hL => by
      rcases List.mem_cons.1 hL with rfl | hL
      · exact ⟨neg a, List.mem_singleton_self _, List.mem_cons_self⟩
      · obtain ⟨c, hc, hcΓ⟩ := hF L hL; exact ⟨c, hc, List.mem_cons_of_mem _ hcΓ⟩
    have k₂ := h₂ (a :: Γ) fun L hL => by
      rcases List.mem_cons.1 hL with rfl | hL
      · exact ⟨a, List.mem_singleton_self _, List.mem_cons_self⟩
      · obtain ⟨c, hc, hcΓ⟩ := hG L hL; exact ⟨c, hc, List.mem_cons_of_mem _ hcΓ⟩
    exact hU.up _ _ (fun x hx => by simpa using hx) (hU.cut k₁ k₂)

end Cnf

/-! ## Semantics -/

section Semantics

variable {M : Type v} {sat : M → C → Prop}

theorem cnfSat_units {m : M} {Γ : List C} :
    CnfSat sat m (units Γ) ↔ Refutation.SatAll sat m Γ := by
  constructor
  · intro h c hc
    obtain ⟨d, hd, hsd⟩ := h [c] (mem_units.2 ⟨c, hc, rfl⟩)
    rw [List.mem_singleton] at hd
    exact hd ▸ hsd
  · intro h K hK
    obtain ⟨c, hc, rfl⟩ := mem_units.1 hK
    exact ⟨c, List.mem_singleton_self c, h c hc⟩

theorem cnfUnsat_closed : CnfClosed (CnfUnsat sat) := by
  refine ⟨fun F G h hF m hm => hF m fun K hK => hm K (h hK), ?_, ?_, ?_⟩
  · intro K K' F hK h m hm
    refine h m fun L hL => ?_
    rcases List.mem_cons.1 hL with rfl | hL
    · obtain ⟨c, hc, hsc⟩ := hm K' List.mem_cons_self
      exact ⟨c, hK hc, hsc⟩
    · exact hm L (List.mem_cons_of_mem _ hL)
  · intro a K F h₁ h₂ m hm
    obtain ⟨c, hc, hsc⟩ := hm _ List.mem_cons_self
    have hF : CnfSat sat m F := fun L hL => hm L (List.mem_cons_of_mem _ hL)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h₁ m fun L hL => by
        rcases List.mem_cons.1 hL with rfl | hL
        · exact ⟨c, List.mem_singleton_self c, hsc⟩
        · exact hF L hL
    · exact h₂ m fun L hL => by
        rcases List.mem_cons.1 hL with rfl | hL
        · exact ⟨c, hc, hsc⟩
        · exact hF L hL
  · intro F m hm
    obtain ⟨_, hc, _⟩ := hm [] List.mem_cons_self
    exact absurd hc List.not_mem_nil

theorem cnfUnsat_complement (hn : NegSound sat neg) (c : C) : CnfUnsat sat [[c], [neg c]] := by
  intro m hm
  obtain ⟨x, hx, hsx⟩ := hm [c] List.mem_cons_self
  obtain ⟨y, hy, hsy⟩ := hm [neg c] (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [List.mem_singleton] at hx hy
  subst hx hy
  exact hn m x hsy hsx

theorem cnfUnsat_unitCut (hn : NegComplete sat neg) {a : C} {F G : List (List C)}
    (h₁ : CnfUnsat sat ([neg a] :: F)) (h₂ : CnfUnsat sat ([a] :: G)) : CnfUnsat sat (F ++ G) := by
  intro m hm
  have hF : CnfSat sat m F := fun K hK => hm K (List.mem_append_left _ hK)
  have hG : CnfSat sat m G := fun K hK => hm K (List.mem_append_right _ hK)
  by_cases ha : sat m a
  · exact h₂ m fun K hK => by
      rcases List.mem_cons.1 hK with rfl | hK
      · exact ⟨a, List.mem_singleton_self a, ha⟩
      · exact hG K hK
  · exact h₁ m fun K hK => by
      rcases List.mem_cons.1 hK with rfl | hK
      · exact ⟨neg a, List.mem_singleton_self _, hn m a ha⟩
      · exact hF K hK

theorem unitsOf_cnfUnsat : unitsOf (CnfUnsat sat) = Refutation.Unsat sat := by
  funext Γ
  exact propext (forall_congr' fun m => not_congr cnfSat_units)

end Semantics

/-! ## Signed formulas -/

section Signed

variable {A : Type u}

@[simp] theorem posAtoms_nil : posAtoms ([] : List (Signed A)) = [] := rfl
@[simp] theorem negAtoms_nil : negAtoms ([] : List (Signed A)) = [] := rfl
@[simp] theorem posAtoms_cons_pos (a : A) (l : List (Signed A)) :
    posAtoms (.pos a :: l) = a :: posAtoms l := rfl
@[simp] theorem posAtoms_cons_neg (a : A) (l : List (Signed A)) :
    posAtoms (.neg a :: l) = posAtoms l := rfl
@[simp] theorem negAtoms_cons_pos (a : A) (l : List (Signed A)) :
    negAtoms (.pos a :: l) = negAtoms l := rfl
@[simp] theorem negAtoms_cons_neg (a : A) (l : List (Signed A)) :
    negAtoms (.neg a :: l) = a :: negAtoms l := rfl

theorem posAtoms_append (l l' : List (Signed A)) :
    posAtoms (l ++ l') = posAtoms l ++ posAtoms l' := List.filterMap_append

theorem negAtoms_append (l l' : List (Signed A)) :
    negAtoms (l ++ l') = negAtoms l ++ negAtoms l' := List.filterMap_append

theorem map_neg_map_pos (l : List A) :
    (l.map Signed.pos).map (fun x => -x) = l.map Signed.neg := by
  simp [List.map_map, Function.comp_def]

theorem posAtoms_map_neg (l : List A) : posAtoms (l.map Signed.neg) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem negAtoms_map_neg (l : List A) : negAtoms (l.map Signed.neg) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem signedUnsat_iff {S : Seq A} {Γ : List (Signed A)} :
    signedUnsat S Γ ↔ S (posAtoms Γ) (negAtoms Γ) := by
  simp [signedUnsat, toUnsat, signedLift]

/-- The members of a signed list, split by sign, are its members. -/
theorem mem_split {x : Signed A} {Γ : List (Signed A)} :
    x ∈ (posAtoms Γ).map Signed.pos ++ (negAtoms Γ).map Signed.neg ↔ x ∈ Γ := by
  cases x with
  | pos a => simp [mem_posAtoms]
  | neg a => simp [mem_negAtoms]

theorem signedLift_negL {S : Seq A} (hw : WeakSubset S) : NegL (fun x => -x) (signedLift S) := by
  intro Γ Δ d h
  cases d with
  | pos a =>
    simp only [signedLift, Signed.neg_pos, posAtoms_cons_pos, negAtoms_cons_pos,
      posAtoms_cons_neg, negAtoms_cons_neg] at h ⊢
    exact hw (fun _ hx => hx) (by mem_tac) h
  | neg a =>
    simp only [signedLift, Signed.neg_neg_atom, posAtoms_cons_pos, negAtoms_cons_pos,
      posAtoms_cons_neg, negAtoms_cons_neg] at h ⊢
    exact hw (by mem_tac) (fun _ hx => hx) h

theorem signedLift_negR {S : Seq A} (hw : WeakSubset S) : NegR (fun x => -x) (signedLift S) := by
  intro Γ Δ g h
  cases g with
  | pos a =>
    simp only [signedLift, Signed.neg_pos, posAtoms_cons_pos, negAtoms_cons_pos,
      posAtoms_cons_neg, negAtoms_cons_neg] at h ⊢
    exact hw (by mem_tac) (fun _ hx => hx) h
  | neg a =>
    simp only [signedLift, Signed.neg_neg_atom, posAtoms_cons_pos, negAtoms_cons_pos,
      posAtoms_cons_neg, negAtoms_cons_neg] at h ⊢
    exact hw (fun _ hx => hx) (by mem_tac) h

theorem gentzenClosed_signedLift {S : Seq A} (hS : Closed defaultRules S) :
    GentzenClosed (fun x => -x) (signedLift S) :=
  ⟨closed_signedLift hS, signedLift_negL hS.weak, signedLift_negR hS.weak⟩

theorem atomSeq_signedUnsat (S : Seq A) : atomSeq (signedUnsat S) = S := by
  funext Γ Δ
  simp only [atomSeq, MultiSystem.posPart, MultiSystem.posPartAlong, System.pullback, viaUnsat,
    map_neg_map_pos, signedUnsat_iff, posAtoms_append, negAtoms_append, posAtoms_map_pos,
    negAtoms_map_pos, posAtoms_map_neg, negAtoms_map_neg, List.append_nil, List.nil_append]

theorem signedUnsat_atomSeq {U : List (Signed A) → Prop} (hU : ListPred.UpClosed U) :
    signedUnsat (atomSeq U) = U := by
  funext Γ
  simp only [signedUnsat_iff, atomSeq, MultiSystem.posPart, MultiSystem.posPartAlong,
    System.pullback, viaUnsat, map_neg_map_pos]
  exact propext ⟨hU _ _ fun _ hx => mem_split.1 hx, hU _ _ fun _ hx => mem_split.2 hx⟩

end Signed

end Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal
