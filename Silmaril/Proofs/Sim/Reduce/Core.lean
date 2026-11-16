module

public import Silmaril.Sim.Reduce.Core.Defs
public import Silmaril.Sim.Wasm.Thms

/-!
# Reducing ISA problems to Wasm problems: proofs (ISA-agnostic core)

The header is `Silmaril/Sim/Reduce/Core/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce

open Silmaril.Machine.Execution (Reaches)

variable {σ W : Type}

/-! ## Reductions and decompositions -/

/-- Refutation transfer along an exact decomposition: a refuted piece refutes the goal. -/
theorem Decomp.Exact.refute {D : Decomp} (hD : D.Exact) {p : Prop} (hp : p ∈ D.pieces)
    (h : ¬ p) : ¬ D.goal :=
  fun hg => h (hD hg p hp)

theorem Decomp.ofReduction_toReduction (d : Decomp) : Decomp.ofReduction d.toReduction = d := rfl

theorem Decomp.toReduction_ofReduction {g : Prop} (r : Silmaril.Sim.Institution.Reduction g) :
    (Decomp.ofReduction r).toReduction = r := rfl

/-- Refutation transfer along an exact legacy reduction. -/
theorem Reduction.Exact.refute (R : Reduction.Exact) : ¬ R.tgt → ¬ R.src :=
  fun h hs => h (R.complete hs)

/-- An exact legacy reduction gives an exact `Decomp`. -/
theorem Reduction.Exact.toDecomp_exact (R : Reduction.Exact) : R.toDecomp.Exact :=
  fun hs p hp => by
    simp only [Reduction.toDecomp, Decomp.single, List.mem_singleton] at hp
    exact hp ▸ R.complete hs

/-- Solve a decomposition from solutions of its pieces. -/
theorem Decomp.solve (D : Decomp) (h : ∀ p ∈ D.pieces, p) : D.goal := D.compose h

/-- Refine one piece `q` of `D` by a decomposition `E` of it. -/
noncomputable def Decomp.refine (D E : Decomp) (q : Prop) (hq : E.goal = q) : Decomp where
  goal := D.goal
  pieces := D.pieces.filter (fun p => @decide (p ≠ q) (Classical.propDecidable _)) ++ E.pieces
  compose h := by
    apply D.compose
    intro p hp
    by_cases hpq : p = q
    · subst hpq
      rw [← hq]
      exact E.compose fun r hr => h r (List.mem_append_right _ hr)
    · exact h p (List.mem_append_left _ (List.mem_filter.mpr ⟨hp, @decide_eq_true _ (Classical.propDecidable _) hpq⟩))

/-- Chain two legacy reductions: `R₂` reduces to a problem that solves `R₁`'s target. Use
`Decomp.refine` on `Decomp`s instead. -/
@[deprecated "use `Decomp.single` and `Decomp.refine`" (since := "2026-11-10")]
def Reduction.trans (R₁ R₂ : Reduction) (h : R₂.src → R₁.tgt) : Reduction where
  src := R₁.src
  tgt := R₂.tgt
  sound t := R₁.sound (h (R₂.sound t))

/-! ## The reduction theorem -/

/-- **Soundness of the reduction**: a solution of the Wasm problem (the pulled-back pre- and
postcondition) solves the ISA problem, for every ISA state the simulator can encode. This is the
run-level form of `Silmaril.Sim.Simulation.reaches`: for `SoundSim.ofSimulation Sim` both state the
same transfer (`wasmTotal_ofSimulation_iff`). -/
theorem isaReach_of_wasmTotal (K : SoundSim σ W) {Init : W → Prop} {Pre : σ → Prop}
    {Post : σ → σ → Prop} (henc : Encodes K Init Pre)
    (h : WasmTotal K Init (pullPre K Pre) (pullPost K Post)) : IsaReach K.step Pre Post := by
  intro s hs
  obtain ⟨w, hi, hr⟩ := henc s hs
  obtain ⟨w', hrun, hp⟩ := h w hi ⟨s, hr, hs⟩
  obtain ⟨s', hreach, hr'⟩ := K.sound w w' s hr hrun
  exact ⟨s', hreach, hp s s' hr hr'⟩

/-- **Completeness of the reduction** on the modelled fragment. -/
theorem wasmTotal_of_isaReach (K : SoundSim σ W) {Init : W → Prop} {Pre : σ → Prop}
    {Post : σ → σ → Prop} (hc : Complete K Init Pre Post) (h : IsaReach K.step Pre Post) :
    WasmTotal K Init (pullPre K Pre) (pullPost K Post) := by
  rintro w hi ⟨s, hr, hp⟩
  obtain ⟨t, hreach, hq⟩ := h s hp
  exact hc w s t hi hr hp hreach hq

/-- The reduction of a reachability problem to the Wasm problem, as data. -/
def reachReduction (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) (Post : σ → σ → Prop)
    (henc : Encodes K Init Pre) : Reduction where
  src := IsaReach K.step Pre Post
  tgt := WasmTotal K Init (pullPre K Pre) (pullPost K Post)
  sound := isaReach_of_wasmTotal K henc

/-- The exact reduction, given completeness on the fragment. -/
def reachExact (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) (Post : σ → σ → Prop)
    (henc : Encodes K Init Pre) (hc : Complete K Init Pre Post) : Reduction.Exact where
  toReduction := reachReduction K Init Pre Post henc
  complete := wasmTotal_of_isaReach K hc

/-- **Counterexample transfer**: a Wasm counterexample gives an ISA counterexample at a state
it represents, given completeness on the fragment. -/
theorem isaCex_of_wasmCex (K : SoundSim σ W) {Init : W → Prop} {Pre : σ → Prop}
    {Post : σ → σ → Prop} (hc : Complete K Init Pre Post) {w : W}
    (h : WasmCex K Init (pullPre K Pre) (pullPost K Post) w) :
    ∃ s, K.R w s ∧ IsaCex K.step Pre Post s := by
  obtain ⟨hi, ⟨s, hr, hp⟩, hn⟩ := h
  refine ⟨s, hr, hp, fun t hreach hq => ?_⟩
  obtain ⟨w', hrun, hq'⟩ := hc w s t hi hr hp hreach hq
  exact hn w' hrun hq'

/-- An ISA counterexample refutes the ISA problem. -/
theorem not_isaReach_of_isaCex {step : σ → Option σ} {Pre : σ → Prop} {Post : σ → σ → Prop}
    {s : σ} (h : IsaCex step Pre Post s) : ¬ IsaReach step Pre Post := by
  intro hr
  obtain ⟨t, ht, hq⟩ := hr s h.1
  exact h.2 t ht hq

/-! ## Decomposition -/

/-- **Assume-guarantee composition** over an acyclic call graph: if every function's judgement
holds assuming its callees', every judgement holds. -/
theorem ag_compose {ι : Type} {J : ι → Prop} {callees : ι → List ι} {rank : ι → Nat}
    (hr : Ranked callees rank) (h : ∀ i, AGPiece J callees i) : ∀ i, J i := by
  intro i
  induction hn : rank i using Nat.strong_induction_on generalizing i with
  | _ n ih => exact h i fun j hj => ih (rank j) (hn ▸ hr i j hj) j rfl

/-- The per-function decomposition of `∀ i ∈ fs, J i`: one assume-guarantee piece per
function of `fs`, which must be closed under callees. -/
def agDecomp {ι : Type} (J : ι → Prop) (callees : ι → List ι) (rank : ι → Nat)
    (hr : Ranked callees rank) (fs : List ι) (hclosed : ∀ i ∈ fs, ∀ j ∈ callees i, j ∈ fs) :
    Decomp where
  goal := ∀ i ∈ fs, J i
  pieces := fs.map (AGPiece J callees)
  compose h := by
    intro i hi
    induction hn : rank i using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      exact h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
        fun j hj => ih (rank j) (hn ▸ hr i j hj) j (hclosed i hi j hj) rfl

/-- **Cut-point composition**: block-level pieces, one per cut, with invariants and a measure,
give reachability of the goal from every cut. -/
theorem cut_compose {ι : Type} {R : W → W → Prop} {Inv : ι → W → Prop} {μ : W → Nat}
    {Q : W → Prop} (h : ∀ c, CutPiece R Inv μ Q c) :
    ∀ c w, Inv c w → ∃ w', Relation.ReflTransGen R w w' ∧ Q w' := by
  intro c w hw
  induction hn : μ w using Nat.strong_induction_on generalizing c w with
  | _ n ih =>
    obtain ⟨w₁, hr₁, hq | ⟨c', hi', hlt⟩⟩ := h c w hw
    · exact ⟨w₁, hr₁, hq⟩
    · obtain ⟨w₂, hr₂, hq₂⟩ := ih (μ w₁) (hn ▸ hlt) c' w₁ hi' rfl
      exact ⟨w₂, hr₁.trans hr₂, hq₂⟩

/-- **A sound simulator from per-method pieces**: if each instruction form's step is backed by
the reference machine, the simulator whose runs are sequences of such steps ending in a
`Halted` state is sound. -/
def SoundSim.ofSteps {κ : Type} (step : σ → Option σ) (R : W → σ → Prop) (form : κ → W → W → Prop)
    (Halted : W → Prop) (h : ∀ k, StepPiece step R form k) : SoundSim σ W where
  step := step
  run w w' := Relation.ReflTransGen (fun a b => ∃ k, form k a b) w w' ∧ Halted w'
  R := R
  sound w w' s hr hrun := by
    obtain ⟨hrun, -⟩ := hrun
    induction hrun with
    | refl => exact ⟨s, Reaches.refl _ _, hr⟩
    | tail _ hab ih =>
      obtain ⟨s₁, h₁, hr₁⟩ := ih
      obtain ⟨k, hk⟩ := hab
      obtain ⟨s₂, h₂, hr₂⟩ := h k _ _ s₁ hr₁ hk
      exact ⟨s₂, h₁.trans h₂, hr₂⟩

/-- **Soundness along refinement**: a simulator whose runs map to runs of a sound simulator
`K₂`, preserving what states represent, is sound (for G ≡ M: the globals simulator from the
memory one, or conversely). -/
def SoundSim.ofRefines {V : Type} (K₂ : SoundSim σ V) (run : W → W → Prop) (R : W → σ → Prop)
    (h : W → V) (hrun : ∀ w w', run w w' → K₂.run (h w) (h w'))
    (hrel : ∀ w s, K₂.R (h w) s ↔ R w s) : SoundSim σ W where
  step := K₂.step
  run := run
  R := R
  sound w w' s hr hrun' := by
    obtain ⟨s', h₁, h₂⟩ := K₂.sound _ _ s ((hrel w s).2 hr) (hrun w w' hrun')
    exact ⟨s', h₁, (hrel w' s').1 h₂⟩

/-- **Wasm problems transfer along simulator refinement**: a solution on `K₁` is a solution on
`K₂` for every freshly loaded `K₂` state that is the image of a freshly loaded `K₁` state. -/
theorem wasmTotal_of_refines {V : Type} {K₁ : SoundSim σ W} {K₂ : SoundSim σ V} {h : W → V}
    (hk : SimRefines K₁ K₂ h) {Init₁ : W → Prop} {Init₂ : V → Prop}
    (himg : ∀ v, Init₂ v → ∃ w, Init₁ w ∧ h w = v) {Pre : σ → Prop} {Post : σ → σ → Prop}
    (hw : WasmTotal K₁ Init₁ (pullPre K₁ Pre) (pullPost K₁ Post)) :
    WasmTotal K₂ Init₂ (pullPre K₂ Pre) (pullPost K₂ Post) := by
  intro v hv hp
  obtain ⟨w, hi, rfl⟩ := himg v hv
  obtain ⟨s, hr, hs⟩ := hp
  obtain ⟨w', hrun, hq⟩ := hw w hi ⟨s, (hk.rel w s).1 hr, hs⟩
  exact ⟨h w', hk.run w w' hrun, fun s s' hr hr' => hq s s' ((hk.rel w s).1 hr) ((hk.rel w' s').1 hr')⟩

/-! ## From the step-level interface: `Simulation` and `ExportSim.Cert` -/

section Bridge

open Silmaril.Sim (Machine Simulation Prog PState WasmSim)

variable {L V S : Type}

/-- **The run-level projection of a simulation** against a deterministic reference
(`Machine.ofStep`), run to completion (`Prog.loop`): `run` is the semantics of `loop`, `R` the
simulation relation. -/
def SoundSim.ofSimulation {step : S → Option S} {view : S → PState L V} {A : Machine Unit L V}
    (Sim : Simulation A (Machine.ofStep step view)) : SoundSim S A.St where
  step := step
  run := A.Sem Prog.loop
  R := Sim.R
  sound w w' s hr hrun := by
    obtain ⟨t, ht, hr'⟩ := Sim.sem (p := Prog.loop) trivial hr hrun
    exact ⟨t, (Machine.ofStep_sem_loop_iff step view s t).1 ht, hr'⟩

/-- The reduction's Wasm problem for such a simulator is its angelic `loop` property. -/
theorem wasmTotal_ofSimulation_iff {step : S → Option S} {view : S → PState L V}
    {A : Machine Unit L V} (Sim : Simulation A (Machine.ofStep step view)) (Init : A.St → Prop)
    (Pre : A.St → Prop) (Post : A.St → A.St → Prop) :
    WasmTotal (SoundSim.ofSimulation Sim) Init Pre Post ↔
      A.HAngelic (fun a => Init a ∧ Pre a) Prog.loop Post := by
  constructor
  · rintro h a ⟨hi, hp⟩
    exact h a hi hp
  · intro h a hi hp
    exact h a ⟨hi, hp⟩

/-- The run-level projection of per-export obligations (`WasmSim.Obligations`). Prefer
`SoundSim.ofExportCert`. -/
def SoundSim.ofObligations {step : S → Option S} {view : S → PState L V}
    {W : WasmSim Unit L V} (O : W.Obligations (Machine.ofStep step view)) :
    SoundSim S W.Store :=
  SoundSim.ofSimulation O.simulation

/-- **A certified Wasm simulator** with one command (its `step` export) against a deterministic
reference, as a run-level `SoundSim`: `run` iterates calls of the export (`Prog.loop`). -/
def SoundSim.ofExportCert {H : Type} {step : S → Option S} {view : S → PState L V}
    {K : Silmaril.Sim.Wasm.ExportSim Unit L V H} (Ct : K.Cert (Machine.ofStep step view)) :
    SoundSim S (Silmaril.Wasm.Execution.Core.Store H) :=
  SoundSim.ofSimulation Ct.simulation

/-- The run of `SoundSim.ofExportCert` contains every single call of the export. -/
theorem SoundSim.ofExportCert_run_of_call {H : Type} {step : S → Option S}
    {view : S → PState L V} {K : Silmaril.Sim.Wasm.ExportSim Unit L V H}
    (Ct : K.Cert (Machine.ofStep step view)) {s s' : Silmaril.Wasm.Execution.Core.Store H}
    (h : K.call () s s') : (SoundSim.ofExportCert Ct).run s s' :=
  Silmaril.Sim.Star.single h

end Bridge

end Silmaril.Sim.Reduce
