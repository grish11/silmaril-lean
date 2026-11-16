module

public import Silmaril.Proofs.Sim.Core.PState

/-!
# Proofs: runs, simulations and the transfer of program properties

Names are in `Silmaril.Sim`, exported by the header `Silmaril/Sim/Core/Thms.lean`.

* `Star.trans`, `Star.single`; `Machine.sem_reduct` (a reduct runs the substituted program);
  `Prog.MonoTests.subst`;
* simulations lift from steps to runs: `Simulation.sem`, `CoSimulation.sem`, `Equiv.fwdSem`;
  they compose (`Simulation.refl`, `Simulation.trans`, …) and survive reducts
  (`Simulation.reduct`, `CoSimulation.reduct`); `Equiv.toSimulation`, `Equiv.toCoSimulation`,
  `Equiv.symm`;
* **transfer**: `Simulation.hAngelic` (general, on hidden states), `Simulation.angelic` (on
  views), `Simulation.progress`, `CoSimulation.hDemonic`, `CoSimulation.demonic`;
  `Machine.angelic_of_demonic` (demonic + progress gives angelic);
* Hoare-style rules for decomposition: `HAngelic.{conseq, skip, seq, choice_left,
  choice_right, star_of_measure}` and `HDemonic.{conseq, skip, seq, choice, star}`.
-/

@[expose] public section

namespace Silmaril.Sim

variable {C C' L L' V : Type}

/-! ## Reflexive-transitive closure -/

theorem Star.single {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  .step h (.refl b)

theorem Star.trans {α : Type} {r : α → α → Prop} {a b c : α} (h₁ : Star r a b)
    (h₂ : Star r b c) : Star r a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Star.mono {α : Type} {r r' : α → α → Prop} (h : ∀ a b, r a b → r' a b) {a b : α}
    (hs : Star r a b) : Star r' a b := by
  induction hs with
  | refl => exact .refl _
  | step h₁ _ ih => exact .step (h _ _ h₁) ih

/-- Simulate a `Star` along a relation that simulates each step. -/
theorem Star.sim {α β : Type} {r : α → α → Prop} {r' : β → β → Prop} {R : α → β → Prop}
    (h : ∀ {a a' b}, R a b → r a a' → ∃ b', r' b b' ∧ R a' b') {a a' : α} {b : β}
    (hab : R a b) (hs : Star r a a') : ∃ b', Star r' b b' ∧ R a' b' := by
  induction hs generalizing b with
  | refl => exact ⟨b, .refl b, hab⟩
  | step h₁ _ ih =>
    obtain ⟨b₁, hb₁, hR₁⟩ := h hab h₁
    obtain ⟨b', hb', hR'⟩ := ih hR₁
    exact ⟨b', .step hb₁ hb', hR'⟩

/-! ## Reducts -/

/-- A reduct runs the substituted program. -/
theorem Machine.sem_reduct (e : L → L') (σ : C → Prog C' L' V) (M : Machine C' L' V)
    (p : Prog C L V) (a b : M.St) :
    (M.reduct e σ).Sem p a b ↔ M.Sem (p.subst e σ) a b := by
  induction p generalizing a b with
  | pick k ih =>
    simp only [Machine.Sem, Prog.subst]
    exact ⟨fun ⟨v, h⟩ => ⟨v, (ih v a b).1 h⟩, fun ⟨v, h⟩ => ⟨v, (ih v a b).2 h⟩⟩
  | skip => exact Iff.rfl
  | cmd c => exact Iff.rfl
  | test g => exact Iff.rfl
  | seq p q ihp ihq =>
    simp only [Machine.Sem, Prog.subst]
    exact ⟨fun ⟨m, h₁, h₂⟩ => ⟨m, (ihp a m).1 h₁, (ihq m b).1 h₂⟩,
      fun ⟨m, h₁, h₂⟩ => ⟨m, (ihp a m).2 h₁, (ihq m b).2 h₂⟩⟩
  | choice p q ihp ihq =>
    simp only [Machine.Sem, Prog.subst]
    exact ⟨fun h => h.elim (fun h => .inl ((ihp a b).1 h)) (fun h => .inr ((ihq a b).1 h)),
      fun h => h.elim (fun h => .inl ((ihp a b).2 h)) (fun h => .inr ((ihq a b).2 h))⟩
  | star p ih =>
    simp only [Machine.Sem, Prog.subst]
    exact ⟨Star.mono fun x y => (ih x y).1, Star.mono fun x y => (ih x y).2⟩

theorem Prog.subst_id (p : Prog C L V) : p.subst id Prog.cmd = p := by
  induction p with
  | pick k ih => simp only [Prog.subst, ih]
  | skip => rfl
  | cmd c => rfl
  | test g => rfl
  | seq p q ihp ihq => simp only [Prog.subst, ihp, ihq]
  | choice p q ihp ihq => simp only [Prog.subst, ihp, ihq]
  | star p ih => simp only [Prog.subst, ih]

theorem Prog.subst_subst {C'' L'' : Type} (e : L → L') (σ : C → Prog C' L' V) (e' : L' → L'')
    (τ : C' → Prog C'' L'' V) (p : Prog C L V) :
    (p.subst e σ).subst e' τ = p.subst (fun l => e' (e l)) (fun c => (σ c).subst e' τ) := by
  induction p with
  | pick k ih => simp only [Prog.subst, ih]
  | skip => rfl
  | cmd c => rfl
  | test g => rfl
  | seq p q ihp ihq => simp only [Prog.subst, ihp, ihq]
  | choice p q ihp ihq => simp only [Prog.subst, ihp, ihq]
  | star p ih => simp only [Prog.subst, ih]

/-- Reducts compose. -/
theorem Machine.reduct_reduct {C'' L'' : Type} (e : L → L') (σ : C → Prog C' L' V)
    (e' : L' → L'') (τ : C' → Prog C'' L'' V) (M : Machine C'' L'' V) :
    (M.reduct e' τ).reduct e σ =
      M.reduct (fun l => e' (e l)) (fun c => (σ c).subst e' τ) := by
  simp only [Machine.reduct]
  congr
  funext c a b
  exact propext (Machine.sem_reduct e' τ M (σ c) a b)

/-- The reduct along the identity is the machine. -/
theorem Machine.reduct_id (M : Machine C L V) : M.reduct id Prog.cmd = M := rfl

theorem Prog.MonoTests.subst {e : L → L'} {σ : C → Prog C' L' V}
    (hσ : ∀ c, (σ c).MonoTests) {p : Prog C L V} (hp : p.MonoTests) :
    (p.subst e σ).MonoTests := by
  induction p with
  | pick k ih => exact fun v => ih v (hp v)
  | skip => trivial
  | cmd c => exact hσ c
  | test g => exact PState.Mono.comap e hp
  | seq p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | choice p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | star p ih => exact ih hp

/-! ## Simulations on runs -/

theorem Prog.allTests_true (p : Prog C L V) : p.AllTests fun _ => True := by
  induction p with
  | pick _ ih => exact fun v => ih v
  | skip => trivial
  | cmd _ => trivial
  | test _ => trivial
  | seq _ _ ihp ihq => exact ⟨ihp, ihq⟩
  | choice _ _ ihp ihq => exact ⟨ihp, ihq⟩
  | star _ ih => exact ih

/-- **A forward simulation lifts from steps to runs**, for programs whose guards satisfy a
class `T` that related states transport. -/
theorem FwdSim.semWith {A B : Machine C L V} (S : FwdSim A B)
    {T : (PState L V → Prop) → Prop}
    (hT : ∀ g, T g → ∀ a b, S.R a b → g (A.view a) → g (B.view b)) {p : Prog C L V}
    (hp : p.AllTests T) {a a' : A.St} {b : B.St} (hab : S.R a b) (h : A.Sem p a a') :
    ∃ b', B.Sem p b b' ∧ S.R a' b' := by
  induction p generalizing a a' b with
  | pick k ih =>
    obtain ⟨v, h⟩ := h
    obtain ⟨b', hb, hR⟩ := ih v (hp v) hab h
    exact ⟨b', ⟨v, hb⟩, hR⟩
  | skip => cases h; exact ⟨b, rfl, hab⟩
  | cmd c => exact S.step hab h
  | test g =>
    obtain ⟨hEq, hg⟩ : a = a' ∧ g (A.view a) := h
    exact ⟨b, ⟨rfl, hT g hp _ _ hab hg⟩, hEq ▸ hab⟩
  | seq p q ihp ihq =>
    obtain ⟨m, h₁, h₂⟩ := h
    obtain ⟨bm, hb₁, hRm⟩ := ihp hp.1 hab h₁
    obtain ⟨b', hb₂, hR'⟩ := ihq hp.2 hRm h₂
    exact ⟨b', ⟨bm, hb₁, hb₂⟩, hR'⟩
  | choice p q ihp ihq =>
    rcases h with h | h
    · obtain ⟨b', hb, hR⟩ := ihp hp.1 hab h; exact ⟨b', .inl hb, hR⟩
    · obtain ⟨b', hb, hR⟩ := ihq hp.2 hab h; exact ⟨b', .inr hb, hR⟩
  | star p ih =>
    exact Star.sim (r := A.Sem p) (r' := B.Sem p) (R := S.R) (fun hR hs => ih hp hR hs) hab h


namespace Simulation

variable {A B D : Machine C L V}

/-- **Soundness lifts from steps to runs** (guards upward closed). -/
theorem sem (S : Simulation A B) {p : Prog C L V} (hp : p.MonoTests) {a a' : A.St} {b : B.St}
    (hab : S.R a b) (h : A.Sem p a a') : ∃ b', B.Sem p b b' ∧ S.R a' b' :=
  S.toFwdSim.semWith (fun _ hg _ _ hR h => hg _ _ (S.view_le hR) h) hp hab h

/-- For an exact simulation, runs of programs with **arbitrary guards** are simulated. -/
theorem semExact (S : Simulation A B) (hx : S.Exact) {p : Prog C L V} {a a' : A.St}
    {b : B.St} (hab : S.R a b) (h : A.Sem p a a') : ∃ b', B.Sem p b b' ∧ S.R a' b' :=
  S.toFwdSim.semWith (T := fun _ => True) (fun _ _ _ _ hR h => (hx hR) ▸ h)
    (Prog.allTests_true p) hab h

/-- The identity simulation. -/
def refl (A : Machine C L V) : Simulation A A where
  R a b := a = b
  view_le h := h ▸ PState.Le.refl _
  step {_ _ a' _} h hs := ⟨a', h ▸ hs, rfl⟩
  load b := ⟨b, rfl, rfl⟩

/-- Simulations compose (transitivity along the simulator lattice). -/
def trans (S : Simulation A B) (T : Simulation B D) : Simulation A D where
  R a d := ∃ b, S.R a b ∧ T.R b d
  view_le := fun ⟨_, h₁, h₂⟩ l v h => T.view_le h₂ l v (S.view_le h₁ l v h)
  step := fun ⟨_, h₁, h₂⟩ hs => by
    obtain ⟨b', hb, hR⟩ := S.step h₁ hs
    obtain ⟨d', hd, hR'⟩ := T.step h₂ hb
    exact ⟨d', hd, b', hR, hR'⟩
  load d := by
    obtain ⟨b, hb, hv⟩ := T.load d
    obtain ⟨a, ha, hv'⟩ := S.load b
    exact ⟨a, ⟨b, ha, hb⟩, hv'.trans hv⟩

/-- Simulations survive reducts along substitutions with upward-closed guards. -/
def reduct {A B : Machine C' L' V} (S : Simulation A B) (e : L → L') (σ : C → Prog C' L' V)
    (hσ : ∀ c, (σ c).MonoTests) : Simulation (A.reduct e σ) (B.reduct e σ) where
  R := S.R
  view_le h := PState.comap_mono e (S.view_le h)
  step h hs := S.sem (hσ _) h hs
  load b := by
    obtain ⟨a, ha, hv⟩ := S.load b
    exact ⟨a, ha, by simp only [Machine.reduct, hv]⟩

end Simulation

theorem Sound.refl (A : Machine C L V) : Sound A A := ⟨Simulation.refl A⟩

theorem Sound.trans {A B D : Machine C L V} (h₁ : Sound A B) (h₂ : Sound B D) : Sound A D :=
  let ⟨S⟩ := h₁; let ⟨T⟩ := h₂; ⟨S.trans T⟩

namespace CoSimulation

variable {A B D : Machine C L V}

/-- Completeness lifts from steps to runs. -/
theorem sem (S : CoSimulation A B) {p : Prog C L V} {a : A.St} {b b' : B.St}
    (hab : S.R a b) (h : B.Sem p b b') : ∃ a', A.Sem p a a' ∧ S.R a' b' := by
  induction p generalizing a b b' with
  | pick k ih =>
    obtain ⟨v, h⟩ := h
    obtain ⟨a', ha, hR⟩ := ih v hab h
    exact ⟨a', ⟨v, ha⟩, hR⟩
  | skip => cases h; exact ⟨a, rfl, hab⟩
  | cmd c => exact S.step hab h
  | test g =>
    obtain ⟨hEq, hg⟩ : b = b' ∧ g (B.view b) := h
    exact ⟨a, ⟨rfl, (S.view_eq hab) ▸ hg⟩, hEq ▸ hab⟩
  | seq p q ihp ihq =>
    obtain ⟨m, h₁, h₂⟩ := h
    obtain ⟨am, ha₁, hRm⟩ := ihp hab h₁
    obtain ⟨a', ha₂, hR'⟩ := ihq hRm h₂
    exact ⟨a', ⟨am, ha₁, ha₂⟩, hR'⟩
  | choice p q ihp ihq =>
    rcases h with h | h
    · obtain ⟨a', ha, hR⟩ := ihp hab h; exact ⟨a', .inl ha, hR⟩
    · obtain ⟨a', ha, hR⟩ := ihq hab h; exact ⟨a', .inr ha, hR⟩
  | star p ih =>
    exact Star.sim (r := B.Sem p) (r' := A.Sem p) (R := fun b a => S.R a b)
      (fun hR hs => ih hR hs) hab h

/-- The identity co-simulation. -/
def refl (A : Machine C L V) : CoSimulation A A where
  R a b := a = b
  view_eq h := h ▸ rfl
  step {_ _ _ b'} h hs := ⟨b', h ▸ hs, rfl⟩
  load b := ⟨b, rfl⟩

/-- Co-simulations compose. -/
def trans (S : CoSimulation A B) (T : CoSimulation B D) : CoSimulation A D where
  R a d := ∃ b, S.R a b ∧ T.R b d
  view_eq := fun ⟨_, h₁, h₂⟩ => (S.view_eq h₁).trans (T.view_eq h₂)
  step := fun ⟨_, h₁, h₂⟩ hs => by
    obtain ⟨b', hb, hR⟩ := T.step h₂ hs
    obtain ⟨a', ha, hR'⟩ := S.step h₁ hb
    exact ⟨a', ha, b', hR', hR⟩
  load d := by
    obtain ⟨b, hb⟩ := T.load d
    obtain ⟨a, ha⟩ := S.load b
    exact ⟨a, b, ha, hb⟩

/-- Co-simulations survive reducts (no condition on guards). -/
def reduct {A B : Machine C' L' V} (S : CoSimulation A B) (e : L → L')
    (σ : C → Prog C' L' V) : CoSimulation (A.reduct e σ) (B.reduct e σ) where
  R := S.R
  view_eq h := by simp only [Machine.reduct, S.view_eq h]
  step h hs := S.sem h hs
  load := S.load

end CoSimulation

theorem Complete.refl (A : Machine C L V) : Complete A A := ⟨CoSimulation.refl A⟩

theorem Complete.trans {A B D : Machine C L V} (h₁ : Complete A B) (h₂ : Complete B D) :
    Complete A D :=
  let ⟨S⟩ := h₁; let ⟨T⟩ := h₂; ⟨S.trans T⟩

namespace Equiv

variable {A B : Machine C L V}

/-- An equivalence is a simulation. -/
def toSimulation (E : Equiv A B) : Simulation A B where
  R := E.R
  view_le h := (E.view_eq h) ▸ PState.Le.refl _
  step := E.fwd
  load b := let ⟨a, h⟩ := E.load b; ⟨a, h, E.view_eq h⟩

/-- An equivalence is a co-simulation. -/
def toCoSimulation (E : Equiv A B) : CoSimulation A B where
  R := E.R
  view_eq := E.view_eq
  step := E.bwd
  load := E.load

/-- Equivalence is symmetric. -/
def symm (E : Equiv A B) : Equiv B A where
  R b a := E.R a b
  view_eq h := (E.view_eq h).symm
  fwd := E.bwd
  bwd := E.fwd
  load := E.store
  store := E.load

end Equiv

/-! ## Transfer of program properties -/

namespace Simulation

variable {A B : Machine C L V}

/-- **Transfer of angelic properties, hidden-state form.** Every `B`-precondition state is
related to an `A`-precondition state, and related `A`-postconditions imply `B`-ones. -/
theorem hAngelic (S : Simulation A B) {p : Prog C L V} (hp : p.MonoTests)
    {PA : A.St → Prop} {PB : B.St → Prop} {QA : A.St → A.St → Prop} {QB : B.St → B.St → Prop}
    (hpre : ∀ b, PB b → ∃ a, S.R a b ∧ PA a)
    (hpost : ∀ a a' b b', S.R a b → S.R a' b' → QA a a' → QB b b')
    (h : A.HAngelic PA p QA) : B.HAngelic PB p QB := by
  intro b hb
  obtain ⟨a, hab, ha⟩ := hpre b hb
  obtain ⟨a', hrun, hq⟩ := h a ha
  obtain ⟨b', hrun', hR'⟩ := S.sem hp hab hrun
  exact ⟨b', hrun', hpost a a' b b' hab hR' hq⟩

/-- **Transfer of angelic properties on views**: a property the simulator has (some run of `p`
from every `P`-view ends `Q`-related) is a property of the reference, when the guards of `p`
and the postcondition are upward closed (what the simulator shows defined is true). -/
theorem angelic (S : Simulation A B) {p : Prog C L V} (hp : p.MonoTests)
    {P : PState L V → Prop} {Q : PState L V → PState L V → Prop}
    (hQ : ∀ x, PState.Mono (Q x)) (h : A.Angelic P p Q) : B.Angelic P p Q := by
  intro b hb
  obtain ⟨a, hab, hv⟩ := S.load b
  obtain ⟨a', hrun, hq⟩ := h a (show P (A.view a) from hv ▸ hb)
  obtain ⟨b', hrun', hR'⟩ := S.sem hp hab hrun
  have hq' : Q (B.view b) (A.view a') := hv ▸ hq
  exact ⟨b', hrun', hQ _ _ _ (S.view_le hR') hq'⟩

/-- Progress transfers along a simulation. -/
theorem progress (S : Simulation A B) {p : Prog C L V} (hp : p.MonoTests)
    {P : PState L V → Prop} (h : A.Progress P p) : B.Progress P p := by
  intro b hb
  obtain ⟨a, hab, hv⟩ := S.load b
  obtain ⟨a', hrun⟩ := h a (show P (A.view a) from hv ▸ hb)
  obtain ⟨b', hrun', _⟩ := S.sem hp hab hrun
  exact ⟨b', hrun'⟩

end Simulation

namespace CoSimulation

variable {A B : Machine C L V}

/-- **Transfer of demonic properties, hidden-state form.** -/
theorem hDemonic (S : CoSimulation A B) {p : Prog C L V}
    {PA : A.St → Prop} {PB : B.St → Prop} {QA : A.St → A.St → Prop} {QB : B.St → B.St → Prop}
    (hpre : ∀ b, PB b → ∃ a, S.R a b ∧ PA a)
    (hpost : ∀ a a' b b', S.R a b → S.R a' b' → QA a a' → QB b b')
    (h : A.HDemonic PA p QA) : B.HDemonic PB p QB := by
  intro b b' hb hrun
  obtain ⟨a, hab, ha⟩ := hpre b hb
  obtain ⟨a', hrun', hR'⟩ := S.sem hab hrun
  exact hpost a a' b b' hab hR' (h a a' ha hrun')

/-- **Transfer of demonic properties on views**: if every run of the (complete) simulator
satisfies `Q`, every run of the reference does. -/
theorem demonic (S : CoSimulation A B) {p : Prog C L V} {P : PState L V → Prop}
    {Q : PState L V → PState L V → Prop} (h : A.Demonic P p Q) : B.Demonic P p Q :=
  S.hDemonic (fun b hb => let ⟨a, hab⟩ := S.load b; ⟨a, hab, (S.view_eq hab) ▸ hb⟩)
    (fun _ _ _ _ h₁ h₂ hq => (S.view_eq h₁) ▸ (S.view_eq h₂) ▸ hq) h

end CoSimulation

namespace Machine

variable {M : Machine C L V}

/-- Demonic correctness and progress give angelic correctness. -/
theorem hAngelic_of_hDemonic {P : M.St → Prop} {p : Prog C L V} {Q : M.St → M.St → Prop}
    (hd : M.HDemonic P p Q) (hp : M.HProgress P p) : M.HAngelic P p Q := fun a ha =>
  let ⟨b, hb⟩ := hp a ha; ⟨b, hb, hd a b ha hb⟩

theorem angelic_of_demonic {P : PState L V → Prop} {p : Prog C L V}
    {Q : PState L V → PState L V → Prop} (hd : M.Demonic P p Q) (hp : M.Progress P p) :
    M.Angelic P p Q :=
  hAngelic_of_hDemonic hd hp

end Machine

/-! ## Hoare-style rules (decomposition by blocks) -/

namespace Machine.HAngelic

variable {M : Machine C L V} {P P' : M.St → Prop} {Q Q' : M.St → M.St → Prop}
  {p q : Prog C L V}

theorem conseq (h : M.HAngelic P p Q) (hP : ∀ a, P' a → P a)
    (hQ : ∀ a b, P' a → Q a b → Q' a b) : M.HAngelic P' p Q' := fun a ha =>
  let ⟨b, hb, hq⟩ := h a (hP a ha); ⟨b, hb, hQ a b ha hq⟩

theorem skip (hQ : ∀ a, P a → Q a a) : M.HAngelic P .skip Q := fun a ha => ⟨a, rfl, hQ a ha⟩

/-- Sequential composition, with the entry state as a ghost. -/
theorem seq {R : M.St → M.St → Prop} (h₁ : M.HAngelic P p R)
    (h₂ : ∀ a, P a → M.HAngelic (R a) q fun _ c => Q a c) : M.HAngelic P (.seq p q) Q :=
  fun a ha =>
    let ⟨m, hm, hr⟩ := h₁ a ha
    let ⟨c, hc, hq⟩ := h₂ a ha m hr
    ⟨c, ⟨m, hm, hc⟩, hq⟩

theorem choice_left (h : M.HAngelic P p Q) : M.HAngelic P (.choice p q) Q := fun a ha =>
  let ⟨b, hb, hq⟩ := h a ha; ⟨b, .inl hb, hq⟩

theorem choice_right (h : M.HAngelic P q Q) : M.HAngelic P (.choice p q) Q := fun a ha =>
  let ⟨b, hb, hq⟩ := h a ha; ⟨b, .inr hb, hq⟩

/-- **Loops by a decreasing measure**: from an invariant state either the exit condition holds,
or one iteration reaches the invariant with a smaller measure. -/
theorem star_of_measure {I : M.St → Prop} {E : M.St → Prop} (μ : M.St → Nat)
    (h : ∀ a, I a → E a ∨ ∃ b, M.Sem p a b ∧ I b ∧ μ b < μ a) :
    M.HAngelic I (.star p) fun _ b => E b := by
  suffices H : ∀ n a, μ a < n → I a → ∃ b, Star (M.Sem p) a b ∧ E b from
    fun a ha => H (μ a + 1) a (Nat.lt_succ_self _) ha
  intro n
  induction n with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ n ih =>
    intro a hμ ha
    rcases h a ha with he | ⟨b, hb, hib, hμb⟩
    · exact ⟨a, .refl a, he⟩
    · obtain ⟨c, hc, he⟩ := ih b (Nat.lt_of_lt_of_le hμb (Nat.le_of_lt_succ hμ)) hib
      exact ⟨c, .step hb hc, he⟩

end Machine.HAngelic

namespace Machine.HDemonic

variable {M : Machine C L V} {P P' : M.St → Prop} {Q Q' : M.St → M.St → Prop}
  {p q : Prog C L V}

theorem conseq (h : M.HDemonic P p Q) (hP : ∀ a, P' a → P a)
    (hQ : ∀ a b, P' a → Q a b → Q' a b) : M.HDemonic P' p Q' := fun a b ha hr =>
  hQ a b ha (h a b (hP a ha) hr)

theorem skip (hQ : ∀ a, P a → Q a a) : M.HDemonic P .skip Q := fun a b ha hr => by
  cases hr; exact hQ a ha

/-- Sequential composition, with the entry state as a ghost. -/
theorem seq {R : M.St → M.St → Prop} (h₁ : M.HDemonic P p R)
    (h₂ : ∀ a, P a → M.HDemonic (R a) q fun _ c => Q a c) : M.HDemonic P (.seq p q) Q :=
  fun a c ha ⟨m, hm, hc⟩ => h₂ a ha m c (h₁ a m ha hm) hc

theorem choice (h₁ : M.HDemonic P p Q) (h₂ : M.HDemonic P q Q) :
    M.HDemonic P (.choice p q) Q := fun a b ha hr =>
  hr.elim (h₁ a b ha) (h₂ a b ha)

/-- **Loops by an invariant.** -/
theorem star {I : M.St → Prop} (h : M.HDemonic I p fun _ b => I b) :
    M.HDemonic I (.star p) fun _ b => I b := by
  intro a b ha hr
  induction hr with
  | refl => exact ha
  | step h₁ _ ih => exact ih (h _ _ ha h₁)

end Machine.HDemonic

end Silmaril.Sim

/-! ## Deterministic reference machines (`Reaches`) and Wasm obligations -/

namespace Silmaril.Sim

open Silmaril.Machine.Execution (run Reaches)

variable {L V : Type}

/-- Running `ofStep` to completion is `Reaches`. -/
theorem Machine.ofStep_sem_loop_iff {S : Type} (step : S → Option S) (view : S → PState L V)
    (s t : S) : (Machine.ofStep step view).Sem Prog.loop s t ↔ Reaches step s t := by
  constructor
  · intro h
    induction h with
    | refl a => exact ⟨0, rfl⟩
    | step h₁ _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [run, Option.bind]; rw [show step _ = _ from h₁]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => cases hn; exact .refl _
    | succ n ih =>
      simp only [run] at hn
      cases hs : step s with
      | none => rw [hs] at hn; cases hn
      | some s' =>
        rw [hs] at hn
        exact .step (show step s = some s' from hs) (ih s' hn)

/-- Angelic correctness of `loop` on `ofStep` is the `FnContract.Spec.Total` shape. -/
theorem Machine.hAngelic_ofStep_iff {S : Type} (step : S → Option S) (view : S → PState L V)
    (P : S → Prop) (Q : S → S → Prop) :
    (Machine.ofStep step view).HAngelic P Prog.loop Q ↔
      ∀ s, P s → ∃ t, Reaches step s t ∧ Q s t := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, hq⟩ := h s hs
    exact ⟨t, (Machine.ofStep_sem_loop_iff step view s t).1 ht, hq⟩
  · intro h s hs
    obtain ⟨t, ht, hq⟩ := h s hs
    exact ⟨t, (Machine.ofStep_sem_loop_iff step view s t).2 ht, hq⟩

/-- **Reduction of a `Reaches` (Spec.Total-shaped) goal on a deterministic ISA to an angelic
property of a sound simulator.** -/
theorem Simulation.reaches {S : Type} {step : S → Option S} {view : S → PState L V}
    {A : Machine Unit L V} (Sim : Simulation A (Machine.ofStep step view))
    {PA : A.St → Prop} {QA : A.St → A.St → Prop} {P : S → Prop} {Q : S → S → Prop}
    (hpre : ∀ s, P s → ∃ a, Sim.R a s ∧ PA a)
    (hpost : ∀ a a' s t, Sim.R a s → Sim.R a' t → QA a a' → Q s t)
    (h : A.HAngelic PA Prog.loop QA) : ∀ s, P s → ∃ t, Reaches step s t ∧ Q s t :=
  (Machine.hAngelic_ofStep_iff step view P Q).1 (Sim.hAngelic (p := Prog.loop) trivial hpre hpost h)

/-- A one-call implementation (e.g. the `run` export) of a program: if every call of `rel` is
a run of `q`, an angelic property of the call is one of `q`. -/
theorem Machine.HAngelic.of_rel {C : Type} {M : Machine C L V} {q : Prog C L V}
    {rel : M.St → M.St → Prop} (hsub : ∀ a b, rel a b → M.Sem q a b) {P : M.St → Prop}
    {Q : M.St → M.St → Prop} (h : ∀ a, P a → ∃ b, rel a b ∧ Q a b) : M.HAngelic P q Q :=
  fun a ha => let ⟨b, hb, hq⟩ := h a ha; ⟨b, hsub a b hb, hq⟩

/-- **A simulation from per-command partial-correctness triples** (one Wasm problem per
export). -/
def Simulation.ofMethods {C : Type} {A B : Machine C L V} (R : A.St → B.St → Prop)
    (view_le : ∀ {a b}, R a b → A.view a ⊑ B.view b)
    (load : ∀ b, ∃ a, R a b ∧ A.view a = B.view b)
    (method : ∀ c b, A.HDemonic (fun a => R a b) (.cmd c)
      (fun _ a' => ∃ b', B.step c b b' ∧ R a' b')) : Simulation A B where
  R := R
  view_le := view_le
  step {c a a' b} h hs := method c b a a' h hs
  load := load

/-- The obligations of a Wasm simulator give its soundness. -/
def WasmSim.Obligations.simulation {C : Type} {W : WasmSim C L V} {B : Machine C L V}
    (O : W.Obligations B) : Simulation W.toMachine B :=
  Simulation.ofMethods O.R O.view_le O.load O.method

theorem WasmSim.Obligations.sound {C : Type} {W : WasmSim C L V} {B : Machine C L V}
    (O : W.Obligations B) : Sound W.toMachine B := ⟨O.simulation⟩

end Silmaril.Sim

/-! ## Exact simulations, general forward simulations, demonic total correctness -/

namespace Silmaril.Sim

variable {C L V : Type}

/-- **Transfer along a forward simulation, hidden-state form** (no view condition: the guards
of `p` must be transported by the relation). -/
theorem FwdSim.hAngelic {A B : Machine C L V} (S : FwdSim A B)
    {T : (PState L V → Prop) → Prop}
    (hT : ∀ g, T g → ∀ a b, S.R a b → g (A.view a) → g (B.view b)) {p : Prog C L V}
    (hp : p.AllTests T)
    {PA : A.St → Prop} {PB : B.St → Prop} {QA : A.St → A.St → Prop} {QB : B.St → B.St → Prop}
    (hpre : ∀ b, PB b → ∃ a, S.R a b ∧ PA a)
    (hpost : ∀ a a' b b', S.R a b → S.R a' b' → QA a a' → QB b b')
    (h : A.HAngelic PA p QA) : B.HAngelic PB p QB := by
  intro b hb
  obtain ⟨a, hab, ha⟩ := hpre b hb
  obtain ⟨a', hrun, hq⟩ := h a ha
  obtain ⟨b', hrun', hR'⟩ := S.semWith hT hp hab hrun
  exact ⟨b', hrun', hpost a a' b b' hab hR' hq⟩

/-- **Exact simulations transfer every angelic property** (any guards, any postcondition):
branching on values the simulator drew from the oracle is allowed. -/
theorem Simulation.angelicExact {A B : Machine C L V} (S : Simulation A B) (hx : S.Exact)
    {p : Prog C L V} {P : PState L V → Prop} {Q : PState L V → PState L V → Prop}
    (h : A.Angelic P p Q) : B.Angelic P p Q := by
  intro b hb
  obtain ⟨a, hab, hv⟩ := S.load b
  obtain ⟨a', hrun, hq⟩ := h a (show P (A.view a) from hv ▸ hb)
  obtain ⟨b', hrun', hR'⟩ := S.semExact hx hab hrun
  refine ⟨b', hrun', show Q (B.view b) (B.view b') from ?_⟩
  rw [← hx hR', ← hv]
  exact hq

theorem ExactSound.sound {A B : Machine C L V} (h : ExactSound A B) : Sound A B :=
  let ⟨S, _⟩ := h; ⟨S⟩

namespace Machine.Must

variable {M : Machine C L V} {c : C} {stop G Q : M.St → Prop}

theorem mono {G' Q' : M.St → Prop} (hG : ∀ a, G a → G' a) (hQ : ∀ a, Q a → Q' a) {a : M.St}
    (h : M.Must c stop G Q a) : M.Must c stop G' Q' a := by
  induction h with
  | done hq => exact .done (hQ _ hq)
  | step hg hs _ ih => exact .step (hG _ hg) hs ih

/-- **Termination by a measure**: from an invariant state either `Q` holds, or the state may
step (in `G`, not stopped) and every successor is invariant with a smaller measure. Each
case is one demonic Wasm triple about the `step` export. -/
theorem of_measure {I : M.St → Prop} (μ : M.St → Nat)
    (h : ∀ a, I a → Q a ∨ (G a ∧ ¬ stop a ∧ ∀ b, M.step c a b → I b ∧ μ b < μ a)) :
    ∀ a, I a → M.Must c stop G Q a := by
  suffices H : ∀ n a, μ a < n → I a → M.Must c stop G Q a from
    fun a ha => H (μ a + 1) a (Nat.lt_succ_self _) ha
  intro n
  induction n with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ n ih =>
    intro a hμ ha
    rcases h a ha with hq | ⟨hg, hs, hb⟩
    · exact .done hq
    · exact .step hg hs fun b hstep =>
        ih b (Nat.lt_of_lt_of_le (hb b hstep).2 (Nat.le_of_lt_succ hμ)) (hb b hstep).1

/-- With progress (a non-stopped `G`-state can step), `Must` gives a run to `Q`. -/
theorem exists_run (hprog : ∀ a, G a → ¬ stop a → ∃ b, M.step c a b) {a : M.St}
    (h : M.Must c stop G Q a) : ∃ b, Star (M.step c) a b ∧ Q b := by
  induction h with
  | done hq => exact ⟨_, .refl _, hq⟩
  | step hg hs _ ih =>
    obtain ⟨b, hb⟩ := hprog _ hg hs
    obtain ⟨d, hd, hq⟩ := ih b hb
    exact ⟨d, .step hb hd, hq⟩

end Machine.Must

/-- **Transfer of demonic total correctness along a co-simulation.** Every reference step is
a simulator step, a stopped reference state is related only to stopped simulator states, and
the guard and goal transfer along the relation: then termination in `Q` of every simulator
run gives it for every reference run (no measure needed on the reference: the simulator's
`Must` is inductive). -/
theorem CoSimulation.must {A B : Machine C L V} (S : CoSimulation A B) {c : C}
    {stopA GA QA : A.St → Prop} {stopB GB QB : B.St → Prop}
    (hstop : ∀ a b, S.R a b → stopB b → stopA a) (hG : ∀ a b, S.R a b → GA a → GB b)
    (hQ : ∀ a b, S.R a b → QA a → QB b) {a : A.St} (h : A.Must c stopA GA QA a) :
    ∀ {b}, S.R a b → B.Must c stopB GB QB b := by
  induction h with
  | done hq => intro b hab; exact .done (hQ _ b hab hq)
  | step hg hs _ ih =>
    intro b hab
    refine .step (hG _ b hab hg) (fun hsb => hs (hstop _ b hab hsb)) fun b' hb' => ?_
    obtain ⟨a', ha', hR'⟩ := S.step hab hb'
    exact ih a' ha' hR'

end Silmaril.Sim

end
