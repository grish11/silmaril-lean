module

public import Silmaril.Games.Abstract.IterUniform.Defs
public import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Uniformity along silent maps: each condition is needed (proofs)

Uniformity holds along a map that is silent, deterministic, trap-free and defined. Dropping any
one of the four, while keeping the other three, breaks it:

* **not silent** (`FullFun.not_iter_uniform_call`): one import call, total and deterministic;
* **may trap** (`FullFun.not_iter_uniform_trap`): always trap, silent and deterministic;
* **nondeterministic** (`not_iter_uniform_nondet`): `h` returns any `n : ℕ`, silently,
  always, and without changing the state. `F` at `n` exits or continues with some `m < n`;
  `G` exits or continues with its argument. Then `h ; F = G ; [inl, inr ∘ h]`, but `iter G`
  may continue forever (silent divergence) and `h ; iter F` cannot: every chain of `F` is
  strictly decreasing. A chain of `G` maps to a chain of `F` only if the choices of `h` along
  it can be made consistently, one step after the other, and here they cannot;
* **undefined** (`not_iter_uniform_undefined`): `h` has no behaviour at all. Both sides of the
  hypothesis are empty, and `iter G` diverges silently where `h ; iter F` has no behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniform

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable (E : Sig.{u})

/-! ## A nondeterministic silent total map -/

/-- Return any natural number, silently, keeping the state. -/
def anyNat : FullFun E PUnit.{u + 1} PUnit.{u + 1} (ULift.{u} ℕ) :=
  (fun s _ => {y | ∃ n : ℕ, y = ([], End.ret ⟨n⟩ s)}, fun _ _ => ∅)

/-- Exit, or continue with a smaller number. -/
def countDown : FullFun E PUnit.{u + 1} (ULift.{u} ℕ) (PUnit.{u + 1} ⊕ ULift.{u} ℕ) :=
  (fun s n => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨ ∃ m < n.down, y = ([], End.ret (.inr ⟨m⟩) s)},
    fun _ _ => ∅)

/-- Exit, or continue with the same argument. -/
def exitOrLoop : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
  (fun s _ => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨ y = ([], End.ret (.inr ⟨⟩) s)}, fun _ _ => ∅)

theorem anyNat_hyp :
    FullFun.seq (anyNat E) (countDown E) =
      FullFun.seq (exitOrLoop E)
        (FullFun.case (FullFun.pure.map Sum.inl) ((anyNat E).map Sum.inr)) := by
  refine Prod.ext (funext fun s => funext fun a => Set.ext fun y => ?_)
    (funext fun s => funext fun a => Set.ext fun ω => ?_)
  · have key : ∀ z, z ∈ (FullFun.seq (anyNat E) (countDown E)).1 s a ↔
        z = ([], End.ret (.inl ⟨⟩) s) ∨ ∃ m : ℕ, z = ([], End.ret (.inr ⟨m⟩) s) := by
      intro z
      constructor
      · rintro (⟨c, ⟨n, hc⟩, -⟩ | ⟨c, ⟨n, hc⟩, -⟩ | ⟨c₁, b, s₁, c₂, e, ⟨n, hc⟩, hm, rfl⟩)
        · cases (Prod.mk.inj hc).2
        · cases (Prod.mk.inj hc).2
        · obtain ⟨rfl, he⟩ := Prod.mk.inj hc
          cases he
          rcases hm with hm | ⟨m, -, hm⟩
          · exact .inl hm
          · exact .inr ⟨m, hm⟩
      · rintro (rfl | ⟨m, rfl⟩)
        · exact .inr (.inr ⟨[], ⟨0⟩, s, [], _, ⟨0, rfl⟩, .inl rfl, rfl⟩)
        · exact .inr (.inr ⟨[], ⟨m + 1⟩, s, [], _, ⟨m + 1, rfl⟩,
            .inr ⟨m, Nat.lt_succ_self m, rfl⟩, rfl⟩)
    rw [key]
    constructor
    · rintro (rfl | ⟨m, rfl⟩)
      · exact .inr (.inr ⟨[], .inl ⟨⟩, s, [], _, .inl rfl, ⟨([], .ret ⟨⟩ s), rfl, rfl⟩, rfl⟩)
      · exact .inr (.inr ⟨[], .inr ⟨⟩, s, [], _, .inr rfl,
          ⟨([], .ret ⟨m⟩ s), ⟨m, rfl⟩, rfl⟩, rfl⟩)
    · rintro (⟨c, hc, -⟩ | ⟨c, hc, -⟩ | ⟨c₁, b, s₁, c₂, e, hc, hm, rfl⟩)
      · rcases hc with hc | hc <;> cases (Prod.mk.inj hc).2
      · rcases hc with hc | hc <;> cases (Prod.mk.inj hc).2
      · rcases hc with hc | hc <;> obtain ⟨rfl, he⟩ := Prod.mk.inj hc <;> cases he
        · obtain ⟨y, rfl, hy⟩ := hm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
          exact .inl rfl
        · obtain ⟨y, ⟨m, rfl⟩, hy⟩ := hm
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
          exact .inr ⟨m, rfl⟩
  · constructor
    · rintro (hω | ⟨_, _, _, _, _, hω, _⟩)
      · exact hω.elim
      · exact hω.elim
    · rintro (hω | ⟨_, b, _, _, _, hω, _⟩)
      · exact hω.elim
      · cases b
        · exact hω.elim
        · exact hω.elim

/-- No finite behaviour of iterating `countDown` diverges: every chain strictly decreases. -/
theorem countDown_iter_not_div {s : PUnit.{u + 1}} {n : ULift.{u} ℕ}
    {y : CallBeh E PUnit.{u + 1} PUnit.{u + 1}} (hy : AFun.IterBeh (countDown E).1 s n y) :
    y.2 ≠ End.div := by
  induction hy with
  | exit => exact fun h => by cases h
  | trap hm => rcases hm with hm | ⟨_, _, hm⟩ <;> cases (Prod.mk.inj hm).2
  | div hm => rcases hm with hm | ⟨_, _, hm⟩ <;> cases (Prod.mk.inj hm).2
  | step _ _ ih => exact ih
  | spin σ _ hσ =>
    intro _
    have hlt : ∀ k, (σ (k + 1)).2.down < (σ k).2.down := fun k => by
      rcases hσ k with hm | ⟨m, hm, he⟩
      · cases (Prod.mk.inj hm).2
      · have h2 : (σ (k + 1)).2 = ⟨m⟩ := by
          simp only [Prod.mk.injEq, End.ret.injEq, Sum.inr.injEq] at he
          exact he.2.1
        rw [h2]
        exact hm
    have hb : ∀ k, (σ k).2.down + k ≤ (σ 0).2.down := fun k => by
      induction k with
      | zero => omega
      | succ k ih => have := hlt k; omega
    have := hb ((σ 0).2.down + 1)
    omega

/-- **Nondeterminism breaks uniformity**, even for a silent map that always returns and
keeps the state. -/
theorem not_iter_uniform_nondet :
    FullFun.Silent (anyNat E) ∧ (∀ s a, AFun.MustReturn (anyNat E).1 s a) ∧
      AFun.StatePreserving (anyNat E).1 ∧ ¬ AFun.Det (anyNat E).1 ∧
      FullFun.seq (anyNat E) (countDown E) =
        FullFun.seq (exitOrLoop E)
          (FullFun.case (FullFun.pure.map Sum.inl) ((anyNat E).map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter (exitOrLoop E)).1 ⟨⟩ ⟨⟩ ∧
      ([], End.div) ∉ (FullFun.seq (anyNat E) (FullFun.iter (countDown E))).1 ⟨⟩ ⟨⟩ := by
  refine ⟨⟨fun _ _ => rfl, fun s a y ⟨n, hy⟩ => by rw [hy]⟩,
    fun s a => ⟨⟨_, 0, rfl⟩, fun y ⟨n, hy⟩ => by rw [hy]; exact id⟩,
    fun s a c b s' ⟨n, hy⟩ => by cases (Prod.mk.inj hy).2; rfl,
    fun hdet => ?_, anyNat_hyp E, ?_, ?_⟩
  · have := hdet ⟨⟩ ⟨⟩ ([], End.ret ⟨0⟩ ⟨⟩) ([], End.ret ⟨1⟩ ⟨⟩) ⟨0, rfl⟩ ⟨1, rfl⟩
    have h01 : (End.ret ⟨0⟩ ⟨⟩ : End PUnit.{u + 1} (ULift.{u} ℕ)) = End.ret ⟨1⟩ ⟨⟩ := this
    cases h01
  · exact AFun.IterBeh.spin (fun _ => (⟨⟩, ⟨⟩)) rfl fun _ => .inr rfl
  · rintro (⟨c, ⟨n, hc⟩, -⟩ | ⟨c, ⟨n, hc⟩, -⟩ | ⟨c₁, b, s₁, c₂, e, ⟨n, hc⟩, hm, he⟩)
    · cases (Prod.mk.inj hc).2
    · cases (Prod.mk.inj hc).2
    · exact countDown_iter_not_div E hm (Prod.mk.inj he).2.symm

/-! ## An undefined silent map -/

/-- No behaviour at all. -/
def noBeh : FullFun E PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1} := (fun _ _ => ∅, fun _ _ => ∅)

/-- Continue silently with the argument. -/
abbrev loopBody : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
  FullFun.pure.map Sum.inr

/-- **An undefined map breaks uniformity**, even when it is silent, deterministic and never
traps or diverges. -/
theorem not_iter_uniform_undefined :
    FullFun.Silent (noBeh E) ∧ AFun.Det (noBeh E).1 ∧ FullFun.NoTrap (noBeh E) ∧
      (∀ s a, ¬ AFun.MayDiv (noBeh E).1 s a) ∧ ¬ FullFun.Defined (noBeh E) ∧
      FullFun.seq (noBeh E) (loopBody E) =
        FullFun.seq (loopBody E)
          (FullFun.case (FullFun.pure.map Sum.inl) ((noBeh E).map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter (loopBody E)).1 ⟨⟩ ⟨⟩ ∧
      (FullFun.seq (noBeh E) (FullFun.iter (loopBody E))).1 ⟨⟩ ⟨⟩ = ∅ := by
  have hempty : ∀ {C : Type u} (X : FullFun E PUnit.{u + 1} PUnit.{u + 1} C) s a,
      (FullFun.seq (noBeh E) X).1 s a = ∅ := fun X s a => by
    ext y
    constructor
    · rintro (⟨_, hc, -⟩ | ⟨_, hc, -⟩ | ⟨_, _, _, _, _, hc, -, -⟩) <;> exact hc.elim
    · intro hy; exact hy.elim
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ hy => hy.elim⟩, fun _ _ _ _ hx => hx.elim,
    fun _ _ ⟨_, hc⟩ => hc, fun _ _ ⟨_, hc⟩ => hc,
    fun hd => (Set.not_nonempty_empty (hd ⟨⟩ ⟨⟩)), ?_, ?_, hempty _ _ _⟩
  · refine Prod.ext (funext fun s => funext fun a => ?_)
      (funext fun s => funext fun a => Set.ext fun ω => ?_)
    · rw [hempty]
      ext y
      constructor
      · intro hy; exact hy.elim
      · rintro (⟨c, ⟨z, rfl, hz⟩, -⟩ | ⟨c, ⟨z, rfl, hz⟩, -⟩ |
          ⟨c₁, b, s₁, c₂, e, ⟨z, rfl, hz⟩, hm, -⟩)
        · cases (Prod.mk.inj hz).2
        · cases (Prod.mk.inj hz).2
        · obtain ⟨-, he⟩ := Prod.mk.inj hz
          cases he
          obtain ⟨_, hm, -⟩ := hm
          exact hm.elim
    · constructor
      · rintro (hω | ⟨_, _, _, _, hc, -, -⟩)
        · exact hω.elim
        · exact hc.elim
      · rintro (hω | ⟨_, b, _, _, -, hω, -⟩)
        · exact hω.elim
        · cases b <;> exact hω.elim
  · exact AFun.IterBeh.spin (fun _ => (⟨⟩, ⟨⟩)) rfl fun _ => ⟨([], .ret ⟨⟩ ⟨⟩), rfl, rfl⟩

/-! ## The known counterexamples, with the conditions they satisfy -/

/-- One import call, as in `FullFun.not_iter_uniform_call`: deterministic, total, not silent. -/
theorem callMap_props {E : Sig.{u}} (x : Call E) :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1} :=
      (fun s a => {([x], End.ret a s)}, fun _ _ => ∅)
    AFun.Det h.1 ∧ (∀ s a, AFun.MustReturn h.1 s a) ∧ FullFun.NoTrap h ∧ FullFun.Defined h ∧
      ¬ FullFun.Silent h := by
  intro h
  obtain ⟨m, n⟩ := x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s a y z hy hz
    rw [hy, hz]
    exact ⟨rfl, fun _ => rfl⟩
  · intro s a
    refine ⟨⟨_, rfl⟩, fun y hy => ?_⟩
    rw [hy]
    exact id
  · rintro s a ⟨c, hc⟩
    cases (Prod.mk.inj hc).2
  · exact fun s a => ⟨_, rfl⟩
  · intro hs
    cases hs.2 ⟨⟩ ⟨⟩ _ rfl

/-- Always trap, as in `FullFun.not_iter_uniform_trap`: silent, deterministic, defined, traps. -/
theorem trapMap_props {E : Sig.{u}} :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1} :=
      (fun _ _ => {([], End.trap)}, fun _ _ => ∅)
    FullFun.Silent h ∧ AFun.Det h.1 ∧ FullFun.Defined h ∧ ¬ FullFun.NoTrap h := by
  intro h
  refine ⟨⟨fun _ _ => rfl, fun s a y hy => by rw [hy]⟩, fun s a y z hy hz => ?_,
    fun s a => ⟨_, rfl⟩, fun hn => hn ⟨⟩ ⟨⟩ ⟨[], rfl⟩⟩
  rw [hy, hz]
  exact (rfl : (End.trap : End PUnit.{u + 1} PUnit.{u + 1}) = End.trap)

/-- **A map making an import call breaks uniformity**, though deterministic and total. -/
theorem not_iter_uniform_call :
    ∃ (E : Sig.{0}) (h : FullFun E PUnit PUnit PUnit) (G : FullFun E PUnit PUnit (PUnit ⊕ PUnit)),
      AFun.Det h.1 ∧ (∀ s a, AFun.MustReturn h.1 s a) ∧ FullFun.NoTrap h ∧ FullFun.Defined h ∧
      ¬ FullFun.Silent h ∧
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G := by
  obtain ⟨E, x, hh⟩ := FullFun.not_iter_uniform_call
  obtain ⟨h1, h2, h3, h4, h5⟩ := callMap_props x
  exact ⟨E, _, _, h1, h2, h3, h4, h5, hh.1, hh.2⟩

/-- **A trapping map breaks uniformity**, though silent, deterministic and defined. -/
theorem not_iter_uniform_trap :
    ∃ (E : Sig.{0}) (h : FullFun E PUnit PUnit PUnit) (G : FullFun E PUnit PUnit (PUnit ⊕ PUnit)),
      FullFun.Silent h ∧ AFun.Det h.1 ∧ FullFun.Defined h ∧ ¬ FullFun.NoTrap h ∧
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G := by
  obtain ⟨E, hh⟩ := FullFun.not_iter_uniform_trap
  obtain ⟨h1, h2, h3, h4⟩ := trapMap_props (E := E)
  exact ⟨E, _, _, h1, h2, h3, h4, hh.1, hh.2⟩

end Silmaril.Proofs.Games.Abstract.IterUniform
