module

public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceMonad.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.MonadProofs

variable {A X Y Z : Type u}

set_option backward.isDefEq.respectTransparency false

theorem prepend_nil (t : Trace A X) : prepend [] t = t := by
  cases t with
  | inl p => cases p; rfl
  | inr s => rfl

theorem prepend_append (w v : List A) (t : Trace A X) :
    prepend (w ++ v) t = prepend w (prepend v t) := by
  cases t with
  | inl p => cases p; simp [prepend, List.append_assoc]
  | inr s => simp [prepend, List.foldr_append]

theorem extend_prepend (k : X → TraceSet A Y) (w : List A) (t : Trace A X) :
    extendTrace k (prepend w t) = prepend w '' extendTrace k t := by
  cases t with
  | inl pair =>
    obtain ⟨v, x⟩ := pair
    change prepend (w ++ v) '' k x = prepend w '' (prepend v '' k x)
    rw [Set.image_image]
    exact congrArg (fun g => g '' k x) (funext (prepend_append w v))
  | inr s => simp [extendTrace, prepend]

theorem bind_prepend (p : TraceSet A X) (k : X → TraceSet A Y) (w : List A) :
    bindTraces (prepend w '' p) k = prepend w '' bindTraces p k := by
  ext t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, ht⟩
    rw [extend_prepend] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact ⟨t', ⟨s, hs, ht'⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, ht⟩, rfl⟩
    refine ⟨prepend w s, ⟨s, hs, rfl⟩, ?_⟩
    rw [extend_prepend]
    exact ⟨_, ht, rfl⟩

private theorem bind_extend (k : X → TraceSet A Y) (l : Y → TraceSet A Z) (s : Trace A X) :
    bindTraces (extendTrace k s) l = extendTrace (fun x => bindTraces (k x) l) s := by
  cases s with
  | inl pair =>
    obtain ⟨w, x⟩ := pair
    exact bind_prepend (k x) l w
  | inr stream =>
    ext t
    change (∃ s ∈ ({Sum.inr stream} : Set (Trace A Y)), t ∈ extendTrace l s) ↔
      t ∈ ({Sum.inr stream} : Set (Trace A Z))
    simp [extendTrace]

private theorem bind_assoc (p : TraceSet A X) (k : X → TraceSet A Y) (l : Y → TraceSet A Z) :
    bindTraces (bindTraces p k) l = bindTraces p (fun x => bindTraces (k x) l) := by
  ext t
  constructor
  · rintro ⟨v, ⟨s, hs, hv⟩, ht⟩
    refine ⟨s, hs, ?_⟩
    rw [← bind_extend]
    exact ⟨v, hv, ht⟩
  · rintro ⟨s, hs, ht⟩
    rw [← bind_extend] at ht
    obtain ⟨v, hv, ht⟩ := ht
    exact ⟨v, ⟨s, hs, hv⟩, ht⟩

private theorem left_unit (x : X) (k : X → TraceSet A Y) :
    bindTraces (pureTrace x) k = k x := by
  ext t
  change (∃ s ∈ ({Sum.inl ([], x)} : Set (Trace A X)), t ∈ extendTrace k s) ↔ t ∈ k x
  simp [extendTrace, prepend_nil]

private theorem right_unit (p : TraceSet A X) : bindTraces p pureTrace = p := by
  have h (s : Trace A X) : extendTrace pureTrace s = {s} := by
    cases s with
    | inl pair => obtain ⟨w, x⟩ := pair; simp [extendTrace, pureTrace, prepend]
    | inr stream => rfl
  ext t
  change (∃ s ∈ p, t ∈ extendTrace pureTrace s) ↔ t ∈ p
  simp [h]

theorem lawfulTraceSet : LawfulMonad (TraceSet A) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := right_unit)
  (pure_bind := left_unit)
  (bind_assoc := bind_assoc)

theorem lawfulNonemptyTrace : LawfulMonad (NonemptyTrace A) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := fun p => Subtype.ext (right_unit p.1))
  (pure_bind := fun x f => Subtype.ext (left_unit x (fun y => (f y).1)))
  (bind_assoc := fun p f g =>
    Subtype.ext (bind_assoc p.1 (fun x => (f x).1) (fun y => (g y).1)))

theorem traceStep_eq_bind (f : X → TraceSet A (Y ⊕ X)) (g : X → TraceSet A Y) (x : X) :
    traceStep f g x = bindTraces (f x) (Sum.elim pureTrace g) := by
  ext t
  constructor
  · rintro (⟨word, y, edge, rfl⟩ | ⟨s, edge, rfl⟩ | ⟨word, x', tail, edge, ht, rfl⟩)
    · refine ⟨.inl (word, .inl y), edge, .inl ([], y), rfl, ?_⟩
      simp [prepend]
    · exact ⟨.inr s, edge, rfl⟩
    · exact ⟨.inl (word, .inr x'), edge, tail, ht, rfl⟩
  · rintro ⟨s, edge, ht⟩
    cases s with
    | inr s => exact Or.inr (Or.inl ⟨s, edge, ht⟩)
    | inl pair =>
      obtain ⟨word, y | x'⟩ := pair
      · obtain ⟨tail, htail, heq⟩ := ht
        change tail = Sum.inl ([], y) at htail
        subst tail
        exact Or.inl ⟨word, y, edge, by simpa only [prepend, List.append_nil] using heq.symm⟩
      · obtain ⟨tail, htail, heq⟩ := ht
        exact Or.inr (Or.inr ⟨word, x', tail, edge, htail, heq.symm⟩)

theorem bind_pureMap (p : TraceSet A X) (h : X → Y) :
    bindTraces p (pureTrace ∘ h) = mapResult h '' p := by
  have he (s : Trace A X) : extendTrace (pureTrace ∘ h) s = {mapResult h s} := by
    cases s with
    | inr s => rfl
    | inl pair => obtain ⟨w, x⟩ := pair; simp [extendTrace, pureTrace, prepend, mapResult]
  ext t
  change (∃ s ∈ p, t ∈ extendTrace (pureTrace ∘ h) s) ↔ t ∈ mapResult h '' p
  simp only [he, Set.mem_singleton_iff, Set.mem_image]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

end Silmaril.Calco2019.Examples.Printing.MonadProofs
