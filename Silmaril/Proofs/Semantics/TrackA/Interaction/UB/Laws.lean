module

public import Silmaril.Semantics.TrackA.Interaction.UB.Defs

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interaction.UB

open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Semantics.TrackA.Interaction.UB

universe u v w

variable {T : Type u} {U : Type v} {V : Type w}

private theorem mem_saturate {s : Explicit T} {o : Option T} :
    o ∈ saturate s ↔ o ∈ s ∨ none ∈ s := Iff.rfl

private theorem mem_bindExplicit {s : Explicit T} {k : T → Explicit U} {o : Option U} :
    o ∈ bindExplicit s k ↔ (o = none ∧ none ∈ s) ∨ ∃ t, some t ∈ s ∧ o ∈ k t := Iff.rfl

theorem collapse_le_collapse_iff (s t : Explicit T) :
    collapse s ≤ collapse t ↔ none ∈ t ∨ s ⊆ t := by
  rw [(insertion T).gc]
  change s ⊆ saturate t ↔ _
  by_cases ub : none ∈ t <;> simp [Set.subset_def, mem_saturate, ub]

theorem val_collapse_of_safe (s : Explicit T) (h : none ∉ s) :
    (collapse s).val = s := by
  ext o
  change o ∈ saturate s ↔ o ∈ s
  simp [mem_saturate, h]

theorem collapse_eq_top_iff (s : Explicit T) : collapse s = ⊤ ↔ none ∈ s := by
  constructor
  · intro eq
    have ub : none ∈ (⊤ : Catastrophic T).val := Set.mem_univ _
    rw [← eq] at ub
    exact (mem_saturate.mp ub).elim id id
  · intro ub
    apply top_unique
    intro o _
    exact Or.inr ub

theorem collapse_inf_of_same_marker (s t : Explicit T) (marker : none ∈ s ↔ none ∈ t) :
    collapse (s ⊓ t) = collapse s ⊓ collapse t := by
  apply Subtype.ext
  ext o
  change o ∈ saturate (s ∩ t) ↔ o ∈ saturate s ∩ saturate t
  simp only [mem_saturate, Set.mem_inter_iff]
  grind

theorem collapse_inf_counterexample (t : T) :
    collapse ({none} ⊓ {some t} : Explicit T) ≠ collapse {none} ⊓ collapse {some t} := by
  rw [(collapse_eq_top_iff _).2 (Set.mem_singleton _), top_inf_eq]
  intro eq
  have present : some t ∈ (collapse ({some t} : Explicit T)).val := Or.inl rfl
  rw [← eq] at present
  have impossible := mem_saturate.mp present
  simp at impossible

theorem val_bot : (⊥ : Catastrophic T).val = ∅ :=
  val_collapse_of_safe ∅ (by simp)

theorem nonempty_iff_ne_bot (x : Catastrophic T) : x.val.Nonempty ↔ x ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, ← val_bot]
  exact Subtype.val_injective.ne_iff

theorem addBottom_le_iff (a b : WithBot (UB.Nonempty T)) :
    addBottom a ≤ addBottom b ↔ a ≤ b := by
  cases a using WithBot.recBotCoe with
  | bot => simp [addBottom]
  | coe a =>
    cases b using WithBot.recBotCoe with
    | bot =>
      have notBot : a.val ≠ ⊥ := (nonempty_iff_ne_bot _).mp a.property
      constructor
      · intro h
        exact (notBot (le_antisymm h bot_le)).elim
      · intro h
        exact (WithBot.coe_ne_bot (le_antisymm h bot_le)).elim
    | coe b => exact (WithBot.coe_le_coe (a := a) (b := b)).symm

theorem addBottom_surjective : Function.Surjective (addBottom (T := T)) := by
  intro a
  by_cases h : a = ⊥
  · exact ⟨⊥, h.symm⟩
  · exact ⟨↑(⟨a, (nonempty_iff_ne_bot a).mpr h⟩ : UB.Nonempty T), rfl⟩

theorem nonempty_sSup (s : Set (Catastrophic T)) (hs : s.Nonempty)
    (all : ∀ x ∈ s, x.val.Nonempty) : (sSup s).val.Nonempty := by
  obtain ⟨x, mem⟩ := hs
  exact (all x mem).mono (show x.val ⊆ (sSup s).val from le_sSup mem)

theorem no_common_lower_bound {x y : T} (different : x ≠ y) :
    ¬ ∃ b : UB.Nonempty T, b ≤ UB.Nonempty.pure x ∧ b ≤ UB.Nonempty.pure y := by
  rintro ⟨b, left, right⟩
  obtain ⟨o, mem⟩ := b.property
  have leftMem : o ∈ (UB.pure x).val := left mem
  have rightMem : o ∈ (UB.pure y).val := right mem
  have singleton (a : T) : (UB.pure a).val = {some a} :=
    val_collapse_of_safe _ (by simp)
  simp only [singleton, Set.mem_singleton_iff] at leftMem rightMem
  exact different (Option.some.inj (leftMem.symm.trans rightMem))

theorem pure_le_all [Subsingleton T] (t : T) (b : UB.Nonempty T) :
    UB.Nonempty.pure t ≤ b := by
  obtain ⟨o, mem⟩ := b.property
  have hasT : some t ∈ b.val.val := by
    cases o with
    | none =>
      have all := b.val.property mem
      rw [all]
      exact Set.mem_univ _
    | some a => rwa [Subsingleton.elim t a]
  intro o present
  change o ∈ (UB.pure t).val at present
  rw [show (UB.pure t).val = {some t} from val_collapse_of_safe _ (by simp)] at present
  exact (Set.mem_singleton_iff.mp present).symm ▸ hasT

private theorem bindExplicit_mono {a b : Explicit T} {f g : T → Explicit U}
    (h : a ⊆ b) (k : ∀ t, f t ⊆ g t) : bindExplicit a f ⊆ bindExplicit b g := by
  intro o mem
  rcases mem_bindExplicit.mp mem with ⟨rfl, input⟩ | ⟨t, input, output⟩
  · exact Or.inl ⟨rfl, h input⟩
  · exact Or.inr ⟨t, h input, k t output⟩

theorem bind_mono {a b : Catastrophic T} {f g : T → Catastrophic U}
    (h : a ≤ b) (k : ∀ t, f t ≤ g t) : bind a f ≤ bind b g :=
  (insertion U).gc.monotone_l (bindExplicit_mono h k)

private theorem bindExplicit_assoc (s : Explicit T) (f : T → Explicit U) (g : U → Explicit V) :
    bindExplicit (bindExplicit s f) g = bindExplicit s (fun t => bindExplicit (f t) g) := by
  ext o
  simp only [mem_bindExplicit, Option.some_ne_none, false_and, false_or]
  grind

private theorem bindExplicit_saturate_left (s : Explicit T) (f : T → Explicit U) :
    saturate (bindExplicit (saturate s) f) = saturate (bindExplicit s f) := by
  ext o
  simp only [mem_saturate, mem_bindExplicit, true_and]
  grind

private theorem bindExplicit_saturate_right (s : Explicit T) (f : T → Explicit U) :
    saturate (bindExplicit s (fun t => saturate (f t))) = saturate (bindExplicit s f) := by
  ext o
  simp only [mem_saturate, mem_bindExplicit, true_and]
  grind

theorem bind_assoc (s : Catastrophic T) (f : T → Catastrophic U) (g : U → Catastrophic V) :
    bind (bind s f) g = bind s (fun t => bind (f t) g) := by
  apply Subtype.ext
  change saturate (bindExplicit (saturate _) _) = saturate (bindExplicit _ (fun _ => saturate _))
  rw [bindExplicit_saturate_left, bindExplicit_saturate_right, bindExplicit_assoc]

theorem pure_bind (t : T) (f : T → Catastrophic U) : bind (UB.pure t) f = f t := by
  change collapse (bindExplicit (UB.pure t).val _) = _
  rw [show (UB.pure t).val = {some t} from val_collapse_of_safe _ (by simp)]
  have exactBind : bindExplicit ({some t} : Explicit T) (fun t => (f t).val) = (f t).val := by
    ext o
    simp [mem_bindExplicit]
  rw [exactBind]
  exact (insertion U).l_u_eq _

theorem bind_pure (s : Catastrophic T) : bind s UB.pure = s := by
  change collapse (bindExplicit s.val fun t => (UB.pure t).val) = _
  have exactBind : bindExplicit s.val (fun t => (UB.pure t).val) = s.val := by
    ext o
    cases o <;> simp [mem_bindExplicit, show ∀ t : T, (UB.pure t).val = {some t} from
      fun t => val_collapse_of_safe _ (by simp), eq_comm]
  rw [exactBind]
  exact (insertion T).l_u_eq _

theorem top_bind (f : T → Catastrophic U) : bind ⊤ f = ⊤ := by
  apply (collapse_eq_top_iff _).2
  exact Or.inl ⟨rfl, Set.mem_univ _⟩

theorem bot_bind (f : T → Catastrophic U) : bind ⊥ f = ⊥ := by
  have empty : bindExplicit (∅ : Explicit T) (fun t => (f t).val) = ∅ := by
    ext o
    simp [mem_bindExplicit]
  change collapse (bindExplicit (⊥ : Catastrophic T).val _) = _
  rw [val_bot, empty]
  rfl

private theorem eq_top_iff_ub (x : Catastrophic T) : x = ⊤ ↔ none ∈ x.val := by
  simpa only [(insertion T).l_u_eq] using collapse_eq_top_iff x.val

theorem bind_eq_top_iff (s : Catastrophic T) (f : T → Catastrophic U) :
    bind s f = ⊤ ↔ s = ⊤ ∨ ∃ t ∈ ordinary s, f t = ⊤ := by
  rw [UB.bind, collapse_eq_top_iff, mem_bindExplicit]
  simp only [eq_top_iff_ub, ordinary, Set.mem_ofPred_eq, true_and]

end Silmaril.Proofs.Semantics.TrackA.Interaction.UB
