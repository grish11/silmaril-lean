module

public import Silmaril.Sim.Machine.Defs
public import Silmaril.Sim.Core.Thms

/-!
# Bridges to Silmaril's machine models: what is proved (header, short proofs inline)

* `must_ofRelIsa_iff`: `Machine.Must` on `ofRelIsa A` with stop `relStop A` is
  `RelIsa.Must A`;
* `relIsaMust_of_coSimulation`: **demonic total correctness transfer** — if `A` is a complete
  simulator of `ofRelIsa I view` (co-simulation), a reference state that may stop is related
  only to simulator states that may stop, and every run of the simulator from a related state
  terminates in `QA` (`Machine.Must`, e.g. by `Machine.Must.of_measure` from per-step Wasm
  triples with a decreasing measure), then `RelIsa.Must I G Q` holds at the reference state.
-/

@[expose] public section

namespace Silmaril.Sim

open Silmaril.X86 (RelIsa)

variable {σ L V : Type}

theorem relIsaMust_of_must (A : RelIsa σ) (view : σ → PState L V) (G Q : σ → Prop)
    {s : (ofRelIsa A view).St} (h : (ofRelIsa A view).Must () (relStop A) G Q s) :
    RelIsa.Must A G Q s := by
  induction h with
  | done hq => exact .done hq
  | step hg hs _ ih => exact .step hg hs ih

theorem must_of_relIsaMust (A : RelIsa σ) (view : σ → PState L V) (G Q : σ → Prop) {s : σ}
    (h : RelIsa.Must A G Q s) : (ofRelIsa A view).Must () (relStop A) G Q s := by
  induction h with
  | done hq => exact .done hq
  | step hg hs _ ih => exact .step hg hs ih

theorem must_ofRelIsa_iff (A : RelIsa σ) (view : σ → PState L V) (G Q : σ → Prop) (s : σ) :
    (ofRelIsa A view).Must () (relStop A) G Q s ↔ RelIsa.Must A G Q s :=
  ⟨relIsaMust_of_must A view G Q, must_of_relIsaMust A view G Q⟩

/-- **Demonic total correctness of a relational reference from a complete simulator.** -/
theorem relIsaMust_of_coSimulation {A : Machine Unit L V} {I : RelIsa σ}
    {view : σ → PState L V} (S : CoSimulation A (ofRelIsa I view)) {stopA GA QA : A.St → Prop}
    {G Q : σ → Prop} (hstop : ∀ a s, S.R a s → I.step s .stop → stopA a)
    (hG : ∀ a s, S.R a s → GA a → G s) (hQ : ∀ a s, S.R a s → QA a → Q s) {a : A.St}
    (h : A.Must () stopA GA QA a) {s : σ} (has : S.R a s) : RelIsa.Must I G Q s :=
  (must_ofRelIsa_iff I view G Q s).1 (S.must hstop hG hQ h has)

end Silmaril.Sim

end
