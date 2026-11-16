module

public import Silmaril.Logic.PDL.Defs

@[expose] public section
namespace Silmaril.Logic.PDL
open CategoryTheory

mutual
  theorem Formula.map_id {S : Signature} (p : Formula S) : p.map (𝟙 S) = p := by
    cases p with
    | atom a => rfl
    | bot => rfl
    | neg p => exact congrArg Formula.neg (Formula.map_id p)
    | conj p q => exact congrArg₂ Formula.conj (Formula.map_id p) (Formula.map_id q)
    | disj p q => exact congrArg₂ Formula.disj (Formula.map_id p) (Formula.map_id q)
    | box a p => exact congrArg₂ Formula.box (Program.map_id a) (Formula.map_id p)
    | diamond a p => exact congrArg₂ Formula.diamond (Program.map_id a) (Formula.map_id p)
  termination_by sizeOf p

  theorem Program.map_id {S : Signature} (a : Program S) : a.map (𝟙 S) = a := by
    cases a with
    | action a => rfl
    | seq a b => exact congrArg₂ Program.seq (Program.map_id a) (Program.map_id b)
    | choice a b => exact congrArg₂ Program.choice (Program.map_id a) (Program.map_id b)
    | star a => exact congrArg Program.star (Program.map_id a)
    | test p => exact congrArg Program.test (Formula.map_id p)
  termination_by sizeOf a
end

mutual
  theorem Formula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
      (p : Formula S) : p.map (f ≫ g) = (p.map f).map g := by
    cases p with
    | atom a => rfl
    | bot => rfl
    | neg p => exact congrArg Formula.neg (Formula.map_comp f g p)
    | conj p q => exact congrArg₂ Formula.conj (Formula.map_comp f g p) (Formula.map_comp f g q)
    | disj p q => exact congrArg₂ Formula.disj (Formula.map_comp f g p) (Formula.map_comp f g q)
    | box a p => exact congrArg₂ Formula.box (Program.map_comp f g a) (Formula.map_comp f g p)
    | diamond a p => exact congrArg₂ Formula.diamond (Program.map_comp f g a) (Formula.map_comp f g p)
  termination_by sizeOf p

  theorem Program.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
      (a : Program S) : a.map (f ≫ g) = (a.map f).map g := by
    cases a with
    | action a => rfl
    | seq a b => exact congrArg₂ Program.seq (Program.map_comp f g a) (Program.map_comp f g b)
    | choice a b => exact congrArg₂ Program.choice (Program.map_comp f g a) (Program.map_comp f g b)
    | star a => exact congrArg Program.star (Program.map_comp f g a)
    | test p => exact congrArg Program.test (Formula.map_comp f g p)
  termination_by sizeOf a
end

mutual
  theorem Formula.holds_map {S T : Signature} (f : S ⟶ T) (M : Model T)
      (p : Formula S) (w : M.World) :
      (p.map f).Holds M w ↔ p.Holds (ModalMu.reduct f M) w := by
    cases p with
    | atom a => rfl
    | bot => rfl
    | neg p => exact not_congr (Formula.holds_map f M p w)
    | conj p q => exact and_congr (Formula.holds_map f M p w) (Formula.holds_map f M q w)
    | disj p q => exact or_congr (Formula.holds_map f M p w) (Formula.holds_map f M q w)
    | box a p =>
        exact forall_congr' fun v => imp_congr (Program.rel_map f M a w v) (Formula.holds_map f M p v)
    | diamond a p =>
        exact exists_congr fun v => and_congr (Program.rel_map f M a w v) (Formula.holds_map f M p v)
  termination_by sizeOf p

  theorem Program.rel_map {S T : Signature} (f : S ⟶ T) (M : Model T)
      (a : Program S) (w v : M.World) :
      (a.map f).Rel M w v ↔ a.Rel (ModalMu.reduct f M) w v := by
    cases a with
    | action a => rfl
    | seq a b => exact exists_congr fun u => and_congr (Program.rel_map f M a w u) (Program.rel_map f M b u v)
    | choice a b => exact or_congr (Program.rel_map f M a w v) (Program.rel_map f M b w v)
    | star a =>
        change Relation.ReflTransGen ((a.map f).Rel M) w v ↔ _
        have he : (a.map f).Rel M = a.Rel (ModalMu.reduct f M) :=
          funext fun x => funext fun y => propext (Program.rel_map f M a x y)
        rw [he]
        rfl
    | test p => exact and_congr Iff.rfl (Formula.holds_map f M p w)
  termination_by sizeOf a
end

 theorem steps_iff_closure {W : Type} (r : W → W → Prop) (w v : W) :
    (∃ n, Steps r n w v) ↔ Relation.ReflTransGen r w v := by
  constructor
  · rintro ⟨n, h⟩
    induction h with
    | zero _ => exact .refl
    | tail _ h ih => exact ih.tail h
  · intro h
    induction h with
    | refl => exact ⟨0, .zero _⟩
    | tail _ h ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, .tail hn h⟩

theorem Program.star_finite {S : Signature} (M : Model S) (a : Program S) (w v : M.World) :
    a.star.Rel M w v ↔ ∃ n, Steps (a.Rel M) n w v :=
  (steps_iff_closure (a.Rel M) w v).symm

theorem Program.star_unfold {S : Signature} (M : Model S) (a : Program S) (w v : M.World) :
    a.star.Rel M w v ↔ w = v ∨ ∃ u, a.Rel M w u ∧ a.star.Rel M u v :=
  Relation.ReflTransGen.cases_head_iff

theorem Formula.diamond_star_unfold {S : Signature} (M : Model S) (a : Program S)
    (p : Formula S) (w : M.World) :
    (Formula.diamond a.star p).Holds M w ↔
      (Formula.disj p (.diamond a (.diamond a.star p))).Holds M w := by
  constructor
  · rintro ⟨v, hpath, hp⟩
    rcases (a.star_unfold M w v).mp hpath with rfl | ⟨u, hu, huv⟩
    · exact Or.inl hp
    · exact Or.inr ⟨u, hu, v, huv, hp⟩
  · rintro (hp | ⟨u, hu, v, huv, hp⟩)
    · exact ⟨w, .refl, hp⟩
    · exact ⟨v, Relation.ReflTransGen.head hu huv, hp⟩

theorem Formula.box_star_unfold {S : Signature} (M : Model S) (a : Program S)
    (p : Formula S) (w : M.World) :
    (Formula.box a.star p).Holds M w ↔
      (Formula.conj p (.box a (.box a.star p))).Holds M w := by
  constructor
  · intro h
    exact ⟨h w .refl, fun u hu v hv => h v (Relation.ReflTransGen.head hu hv)⟩
  · rintro ⟨hp, hstep⟩ v hv
    rcases (a.star_unfold M w v).mp hv with rfl | ⟨u, hu, huv⟩
    · exact hp
    · exact hstep u hu v huv

end Silmaril.Logic.PDL
