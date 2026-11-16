module

public import Silmaril.Proofs.Sim.Core.Run

/-!
# Proofs: state representations (G ≡ M) and specialisation (L)

Names are in `Silmaril.Sim`, exported by `Silmaril/Sim/Core/Thms.lean`.

* `Equiv.refl`, `Equiv.trans`, `Equiv.sem` (both directions, any guards: views are equal),
  **`Equiv.reduct`**: an equivalence of *representations* (machines over accessor commands
  `$rget $rset $fget $fset $fset6`, value-indexed) lifts to the simulators obtained by the same
  core (a derived substitution `σ` of programs over accessors for methods);
  `Sound.of_equiv`, **`Sound.of_repr`**: soundness of the G simulator gives soundness of the M
  simulator, from an equivalence of the two accessor machines only;
* `FwdSim.refl`, `FwdSim.trans`, `Simulation.toFwdSim_trans`; **`FwdSim.block_transfer`**: the
  L representation (registers as locals, methods inlined) — if each inlined method chunk is
  simulated by the corresponding method of the G/M simulator, an angelic property of the
  specialised straight-line program is one of the ISA.
-/

@[expose] public section

namespace Silmaril.Sim

variable {C C' L L' V : Type}

namespace Equiv

/-- The identity equivalence. -/
def refl (A : Machine C L V) : Equiv A A where
  R a b := a = b
  view_eq h := h ▸ rfl
  fwd {_ _ a' _} h hs := ⟨a', h ▸ hs, rfl⟩
  bwd {_ _ _ b'} h hs := ⟨b', h ▸ hs, rfl⟩
  load b := ⟨b, rfl⟩
  store a := ⟨a, rfl⟩

/-- Equivalences compose. -/
def trans {A B D : Machine C L V} (E : Equiv A B) (F : Equiv B D) : Equiv A D where
  R a d := ∃ b, E.R a b ∧ F.R b d
  view_eq := fun ⟨_, h₁, h₂⟩ => (E.view_eq h₁).trans (F.view_eq h₂)
  fwd := fun ⟨_, h₁, h₂⟩ hs => by
    obtain ⟨b', hb, hR⟩ := E.fwd h₁ hs
    obtain ⟨d', hd, hR'⟩ := F.fwd h₂ hb
    exact ⟨d', hd, b', hR, hR'⟩
  bwd := fun ⟨_, h₁, h₂⟩ hs => by
    obtain ⟨b', hb, hR'⟩ := F.bwd h₂ hs
    obtain ⟨a', ha, hR⟩ := E.bwd h₁ hb
    exact ⟨a', ha, b', hR, hR'⟩
  load d := by
    obtain ⟨b, hb⟩ := F.load d
    obtain ⟨a, ha⟩ := E.load b
    exact ⟨a, b, ha, hb⟩
  store a := by
    obtain ⟨b, hb⟩ := E.store a
    obtain ⟨d, hd⟩ := F.store b
    exact ⟨d, b, hb, hd⟩

theorem toSimulation_exact {A B : Machine C L V} (E : Equiv A B) : E.toSimulation.Exact :=
  fun h => E.view_eq h

/-- An equivalence on programs, forwards (any guards). -/
theorem sem {A B : Machine C L V} (E : Equiv A B) {p : Prog C L V} {a a' : A.St} {b : B.St}
    (hab : E.R a b) (h : A.Sem p a a') : ∃ b', B.Sem p b b' ∧ E.R a' b' :=
  E.toSimulation.semExact E.toSimulation_exact hab h

/-- An equivalence on programs, backwards. -/
theorem semBwd {A B : Machine C L V} (E : Equiv A B) {p : Prog C L V} {a : A.St} {b b' : B.St}
    (hab : E.R a b) (h : B.Sem p b b') : ∃ a', A.Sem p a a' ∧ E.R a' b' :=
  E.toCoSimulation.sem hab h

/-- **Representation equivalence lifts through a core**: equivalent accessor machines give
equivalent simulators for every substitution of accessor programs for methods. -/
def reduct {A B : Machine C' L' V} (E : Equiv A B) (e : L → L') (σ : C → Prog C' L' V) :
    Equiv (A.reduct e σ) (B.reduct e σ) where
  R := E.R
  view_eq h := by simp only [Machine.reduct, E.view_eq h]
  fwd h hs := E.sem h hs
  bwd h hs := E.semBwd h hs
  load := E.load
  store := E.store

end Equiv

/-- Soundness transfers along an equivalence of simulators. -/
theorem Sound.of_equiv {A A' B : Machine C L V} (E : Equiv A' A) (h : Sound A B) : Sound A' B :=
  Sound.trans ⟨E.toSimulation⟩ h

/-- **G ≡ M reduced to the accessors.** Two representations `G`, `M` (machines over accessor
commands), one core `σ` (each method a program over accessors): if `M` and `G` are equivalent
as accessor machines, soundness of the G simulator gives soundness of the M simulator. -/
theorem Sound.of_repr {G M : Machine C' L' V} (E : Equiv M G) (e : L → L')
    (σ : C → Prog C' L' V) {B : Machine C L V} (h : Sound (G.reduct e σ) B) :
    Sound (M.reduct e σ) B :=
  Sound.of_equiv (E.reduct e σ) h

/-! ## Forward simulations: composition and the L representation -/

/-- The identity forward simulation. -/
def FwdSim.refl (A : Machine C L V) : FwdSim A A where
  R a b := a = b
  step {_ _ a' _} h hs := ⟨a', h ▸ hs, rfl⟩

/-- Forward simulations compose. -/
def FwdSim.trans {A B D : Machine C L V} (S : FwdSim A B) (T : FwdSim B D) : FwdSim A D where
  R a d := ∃ b, S.R a b ∧ T.R b d
  step := fun ⟨_, h₁, h₂⟩ hs => by
    obtain ⟨b', hb, hR⟩ := S.step h₁ hs
    obtain ⟨d', hd, hR'⟩ := T.step h₂ hb
    exact ⟨d', hd, b', hR, hR'⟩

/-- A block has no guards. -/
theorem Prog.block_allTests {T : (PState L V → Prop) → Prop} (cs : List C) :
    (Prog.block cs : Prog C L V).AllTests T := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨trivial, ih⟩

/-- **Specialisation (L) is sound, straight-line code.** `Lm` is the specialised form (state:
the locals of one function; command `c`: the inlined body of method `c` with constant
operands), `G` the simulator, `B` the reference. If each inlined chunk is simulated by its
method (`FwdSim Lm G`: the problem "inlining a method is sound"), and `G` is sound for `B`,
then an angelic property of the specialised block `cs` (the reduction's problem form) is one of
the reference, through the composed relation. -/
theorem FwdSim.block_transfer {Lm G B : Machine C L V} (SL : FwdSim Lm G) (SG : Simulation G B)
    (cs : List C) {PL : Lm.St → Prop} {PB : B.St → Prop} {QL : Lm.St → Lm.St → Prop}
    {QB : B.St → B.St → Prop}
    (hpre : ∀ b, PB b → ∃ x, (SL.trans SG.toFwdSim).R x b ∧ PL x)
    (hpost : ∀ x x' b b', (SL.trans SG.toFwdSim).R x b → (SL.trans SG.toFwdSim).R x' b' →
      QL x x' → QB b b')
    (h : Lm.HAngelic PL (Prog.block cs) QL) : B.HAngelic PB (Prog.block cs) QB := by
  exact (SL.trans SG.toFwdSim).hAngelic (T := fun _ => False) (fun _ h => h.elim)
    (Prog.block_allTests cs) hpre hpost h

end Silmaril.Sim

end
