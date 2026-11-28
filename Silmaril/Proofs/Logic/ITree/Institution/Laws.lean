module

public import Silmaril.Logic.ITree.Institution.Defs

public section

namespace Silmaril.Logic.ITree.Proofs

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

variable {S T U : Signature.{u}} {E : Type u → Type u} {A : Type v} {X Y : Type w}

theorem reduct_id (M : Model.{u,w} S) : M.reduct (𝟙 S) = M := by
  cases M with
  | mk state initial step =>
    apply congrArg (Model.mk state initial)
    funext q x r y
    apply propext
    exact ⟨fun ⟨r', eq, h⟩ => eq ▸ h, fun h => ⟨r, rfl, h⟩⟩

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (M : Model.{u,w} U) :
    M.reduct (f ≫ g) = (M.reduct g).reduct f := by
  cases M with
  | mk state initial step =>
    apply congrArg (Model.mk state initial)
    funext q x r y
    apply propext
    constructor
    · rintro ⟨z, h, hz⟩
      exact ⟨g.reply (f.request q) z, h, z, rfl, hz⟩
    · rintro ⟨z, h, z', eq, hz⟩
      exact ⟨z', (congrArg (f.reply q) eq).trans h, hz⟩

theorem runs_ret (step : Handler X E) (x : X) (a b : A) :
    Runs step a 0 x (ret b) ↔ b = a := by
  simp [Runs, Part.eq_some_iff, eq_comm]

theorem runs_vis (step : Handler X E) (q : Request E) (k : q.1 → Tree E A)
    (x : X) (n : Nat) (a : A) :
    Runs step a (n + 1) x (vis q.2 k) ↔ ∃ r y, step q x r y ∧ Runs step a n y (k r) := by
  rcases q with ⟨R, ev⟩
  simp [Runs]

theorem runs_iff_handledTrace (step : Handler X E) (n : Nat) (x : X)
    (t : Tree E A) (a : A) :
    Runs step a n x t ↔ ∃ p, TraceReturns a n p ∧ HandledTrace step x t p := by
  induction n generalizing x t with
  | zero =>
    constructor
    · intro h
      exact ⟨.result a, rfl, h, trivial⟩
    · rintro ⟨p, hp, h⟩
      cases p with
      | result b =>
        change b = a at hp
        subst b
        exact h.1
      | «prefix» | request | exchange => exact hp.elim
  | succ n ih =>
    constructor
    · rintro ⟨node, hn, run⟩
      cases node with
      | ret => exact run.elim
      | vis ev k =>
        obtain ⟨r, y, hy, hrun⟩ := run
        obtain ⟨p, hp, ht, hr⟩ := (ih y (k r)).mp hrun
        exact ⟨.exchange ev r p, hp, ⟨k, Part.eq_some_iff.mpr hn, ht⟩, y, hy, hr⟩
    · rintro ⟨p, hp, ht, hr⟩
      cases p with
      | exchange ev r tail =>
        obtain ⟨k, hk, ht⟩ := ht
        obtain ⟨y, hy, hr⟩ := hr
        exact ⟨.vis ev k, Part.eq_some_iff.mp hk, r, y, hy, (ih y (k r)).mpr ⟨tail, hp, ht, hr⟩⟩
      | «prefix» | request | result => exact hp.elim

/-- The operational form of satisfaction, including the reverse direction for
noninjective request maps and nonsurjective reply maps. The source tree fixes
the current request. A target execution supplies the witnesses for reduct. -/
theorem runs_translate (f : S ⟶ T) (step : Handler X T.Event) (n : Nat)
    (x : X) (t : Tree S.Event A) (a : A) :
    Runs step a n x (f.tree id t) ↔ Runs (f.restrict step) a n x t := by
  induction n generalizing x t with
  | zero =>
    simp only [Runs, f.out_tree, Part.eq_some_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨node, h, eq⟩
      cases node <;> simp_all [Signature.Hom.visible]
    · intro h
      exact ⟨.ret a, h, rfl⟩
  | succ n ih =>
    simp only [Runs, f.out_tree]
    constructor
    · rintro ⟨_, hm, run⟩
      obtain ⟨node, h, rfl⟩ := (Part.mem_map_iff _).mp hm
      refine ⟨node, h, ?_⟩
      cases node with
      | ret => exact run
      | @vis R ev k =>
        let q : Request S.Event := ⟨R, ev⟩
        obtain ⟨r, y, hr, hy⟩ := run
        exact ⟨f.reply q r, y, ⟨r, rfl, hr⟩, (ih _ _).mp hy⟩
    · rintro ⟨node, h, run⟩
      refine ⟨_, (Part.mem_map_iff _).mpr ⟨node, h, rfl⟩, ?_⟩
      cases node with
      | ret => exact run
      | vis ev k =>
        obtain ⟨_, y, ⟨r, rfl, hr⟩, hy⟩ := run
        exact ⟨r, y, hr, (ih _ _).mpr hy⟩

theorem runs_renameState (M : Model.{u,w} S) (e : M.State ≃ X)
    (n : Nat) (x : M.State) (t : Tree S.Event A) (a : A) :
    Runs (M.renameState e).step a n (e x) t ↔ Runs M.step a n x t := by
  induction n generalizing x t with
  | zero => rfl
  | succ n ih =>
    simp only [Runs]
    apply exists_congr
    intro node
    apply and_congr_right
    intro _
    cases node with
    | ret => rfl
    | vis ev k =>
      apply exists_congr
      intro r
      constructor
      · rintro ⟨y, hy, run⟩
        refine ⟨e.symm y, ?_, (ih (e.symm y) (k r)).mp ?_⟩
        · simpa only [Model.renameState, Equiv.symm_apply_apply] using hy
        · rw [e.apply_symm_apply y]
          exact run
      · rintro ⟨y, hy, run⟩
        exact ⟨e y, by simpa only [Model.renameState, Equiv.symm_apply_apply] using hy,
          (ih _ _).mpr run⟩

theorem sat_renameState (M : Model.{u,w} S) (e : M.State ≃ X) (φ : Sentence.{u,v} S) :
    Sat (M.renameState e) φ ↔ Sat M φ := by
  constructor
  · intro h x hx n a run
    exact h (e x) (by simpa [Model.renameState] using hx) n a
      ((runs_renameState M e n x φ.program a).mpr run)
  · intro h x hx n a run
    obtain ⟨y, rfl⟩ := e.surjective x
    exact h y (by simpa [Model.renameState] using hx) n a
      ((runs_renameState M e n y φ.program a).mp run)

end Silmaril.Logic.ITree.Proofs
