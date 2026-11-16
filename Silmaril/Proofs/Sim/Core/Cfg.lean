module

public import Silmaril.Proofs.Sim.Core.Repr

/-!
# Proofs: block graphs (control flow in the L-form) and their transfer

Names are in `Silmaril.Sim`, exported by `Silmaril/Sim/Core/Thms.lean`.

* `Machine.sem_choiceList_iff`, `Prog.choiceList_allTests`, `Prog.cfg_allTests`;
* cut-point rules: **`Machine.HAngelic.cfg_of_measure`** (invariant at the cut points and a
  decreasing measure: the reduction's `@invariant` at loop headers), `Machine.HDemonic.cfg`;
* **`FwdSim.prog_transfer`**: the L-form with control flow. If each L command (inlined
  method) is simulated by the simulator's method with equal views (locals hold what the
  globals hold), and the simulator is sound for the reference, an angelic property of any
  L program with upward-closed guards (branches on defined flags, a dispatcher on `pc`) is a
  property of the reference program.
-/

@[expose] public section

namespace Silmaril.Sim

variable {C L V : Type}

theorem Machine.sem_choiceList_iff (M : Machine C L V) (ps : List (Prog C L V)) (a b : M.St) :
    M.Sem (Prog.choiceList ps) a b ↔ ∃ p ∈ ps, M.Sem p a b := by
  induction ps with
  | nil => simp [Prog.choiceList, Machine.Sem]
  | cons p ps ih =>
    cases ps with
    | nil => simp [Prog.choiceList]
    | cons q qs =>
      simp only [Prog.choiceList] at ih ⊢
      simp only [Machine.Sem, ih, List.mem_cons, exists_eq_or_imp]

theorem Prog.choiceList_allTests {T : (PState L V → Prop) → Prop} (hF : T fun _ => False)
    {ps : List (Prog C L V)} (h : ∀ p ∈ ps, p.AllTests T) : (Prog.choiceList ps).AllTests T := by
  induction ps with
  | nil => exact hF
  | cons p ps ih =>
    cases ps with
    | nil => exact h p (List.mem_singleton_self p)
    | cons q qs =>
      exact ⟨h p (List.mem_cons_self ..), ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem Prog.cfg_allTests {T : (PState L V → Prop) → Prop} (hF : T fun _ => False)
    {ps : List (Prog C L V)} {exit : PState L V → Prop} (h : ∀ p ∈ ps, p.AllTests T)
    (he : T exit) : (Prog.cfg ps exit).AllTests T :=
  ⟨Prog.choiceList_allTests hF h, he⟩

/-- **Cut points, angelic**: from an invariant state, either leave (the exit guard holds, and
`E`), or some block runs to an invariant state with a smaller measure. -/
theorem Machine.HAngelic.cfg_of_measure {M : Machine C L V} {blocks : List (Prog C L V)}
    {exit : PState L V → Prop} {I E : M.St → Prop} (μ : M.St → Nat)
    (h : ∀ a, I a → (E a ∧ exit (M.view a)) ∨
      ∃ p ∈ blocks, ∃ b, M.Sem p a b ∧ I b ∧ μ b < μ a) :
    M.HAngelic I (Prog.cfg blocks exit) fun _ b => E b := by
  have hs := Machine.HAngelic.star_of_measure (p := Prog.choiceList blocks)
    (E := fun a => E a ∧ exit (M.view a)) μ fun a ha => by
      rcases h a ha with he | ⟨p, hp, b, hb, hi, hμ⟩
      · exact .inl he
      · exact .inr ⟨b, (M.sem_choiceList_iff blocks a b).2 ⟨p, hp, hb⟩, hi, hμ⟩
  intro a ha
  obtain ⟨b, hb, he, hx⟩ := hs a ha
  exact ⟨b, ⟨b, hb, rfl, hx⟩, he⟩

/-- **Cut points, demonic**: an invariant kept by every block holds, with the exit guard, at
every exit. -/
theorem Machine.HDemonic.cfg {M : Machine C L V} {blocks : List (Prog C L V)}
    {exit : PState L V → Prop} {I : M.St → Prop}
    (h : ∀ p ∈ blocks, M.HDemonic I p fun _ b => I b) :
    M.HDemonic I (Prog.cfg blocks exit) fun _ b => I b ∧ exit (M.view b) := by
  have hs := Machine.HDemonic.star (p := Prog.choiceList blocks) (I := I) fun a b ha hr => by
    obtain ⟨p, hp, hr⟩ := (M.sem_choiceList_iff blocks a b).1 hr
    exact h p hp a b ha hr
  rintro a c ha ⟨b, hb, rfl, hx⟩
  exact ⟨hs a b ha hb, hx⟩

/-- **The L-form with control flow transfers.** `Lm` is the specialised program's machine
(command = inlined method), `G` the simulator, `B` the reference. `SL` simulates each inlined
method by the method itself with equal views; `SG` is the simulator's soundness. Then an
angelic property of any L program with upward-closed guards is one of the reference. -/
theorem FwdSim.prog_transfer {Lm G B : Machine C L V} (SL : FwdSim Lm G)
    (hL : ∀ x a, SL.R x a → Lm.view x = G.view a) (SG : Simulation G B) {p : Prog C L V}
    (hp : p.MonoTests) {PL : Lm.St → Prop} {PB : B.St → Prop} {QL : Lm.St → Lm.St → Prop}
    {QB : B.St → B.St → Prop}
    (hpre : ∀ b, PB b → ∃ x, (SL.trans SG.toFwdSim).R x b ∧ PL x)
    (hpost : ∀ x x' b b', (SL.trans SG.toFwdSim).R x b → (SL.trans SG.toFwdSim).R x' b' →
      QL x x' → QB b b')
    (h : Lm.HAngelic PL p QL) : B.HAngelic PB p QB :=
  (SL.trans SG.toFwdSim).hAngelic (T := PState.Mono)
    (fun _ hg x _ ⟨a, hxa, hab⟩ hx => hg _ _ (SG.view_le hab) (hL x a hxa ▸ hx)) hp hpre hpost h

end Silmaril.Sim

end
