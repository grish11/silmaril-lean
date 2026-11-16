module

public import Silmaril.Wasm.Game.IOAccept.Defs
public import Silmaril.Wasm.Game.Accept.Thms
public import Silmaril.Semantics.Accept.IO.Thms
import Silmaril.Proofs.Wasm.Game.IOAccept.Basic

/-! # Traced I/O acceptance of core Wasm modules: theorems

* **Erasure**: a traced session is a session (`TSession.toSession`), and every session is
  traced with some tag list (`Session.exists_tsession`); so the callouts of a module are those
  of its traced sessions (`callouts_eq_traced`), and `calloutAt?` computes `CalloutOf`
  (`calloutAt?_eq_some_iff`).
* **Traced acceptance refines `Callouts`**: every output of a run, in the input-window or the
  entry reading, is the `callOut` of a reachable callout (`exists_callout_of_mem_ioRuns`,
  `exists_callout_of_mem_entryIORuns`), and every input of a window is read off one
  (`exists_callout_of_input_ioRuns`). With the output role `outputVia imp dec`, every
  triggered output is accepted (`mem_accepted_of_mem_triggers`,
  `mem_accepted_of_mem_entryTriggers`).
* **Monotonicity** in the environment class (`tagTraces_mono`, `ioRuns_mono`,
  `entryIORuns_mono`), as `callouts_mono`.
* **Scope**: traced sessions are flat (`TSession.openScan_eq`: no reentrancy); nothing is
  entered during instantiation (`TSession.no_enter_of_inst`), and its tags are dropped by
  `bracket` (`TSession.bracket_eq`, `TSession.bracket_eq_nil_of_inst`): internal outputs
  outside any invocation trigger nothing.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.IOAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Accept.IO

variable {X I O C : Type}

theorem calloutAt?_eq_some_iff {m : Module} {memAddr : Option Nat} {c : Config Nat}
    {o : Callout} : calloutAt? m memAddr c = some o ↔ CalloutOf m memAddr c o :=
  Silmaril.Proofs.Wasm.Game.IOAccept.calloutAt?_eq_some_iff

theorem outputVia_eq_some_iff {α : Type} {imp : String × String} {dec : Callout → Option α}
    {o : Callout} {b : α} : outputVia imp dec o = some b ↔ o.imp = imp ∧ dec o = some b := by
  unfold outputVia; split <;> simp_all

/-! ## Erasure -/

section Session

variable {P : Profile} {L : SEnv UImp} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}

/-- **A traced session is a session** (forgetting the tags; `run` and `idle` are the started
phase). -/
theorem TSession.toSession {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    Session P L c₀ q₀ addrs p.started x :=
  Silmaril.Proofs.Wasm.Game.IOAccept.toSession h

/-- **Every session is traced**, with some phase, flag and tags. -/
theorem Session.exists_tsession {b : Bool} {x : Config Nat × L.S}
    (h : Session P L c₀ q₀ addrs b x) :
    ∃ (p : Phase) (w : Bool) (ts : List (Tag X I O C)), p.started = b ∧
      TSession P L m memAddr R c₀ q₀ addrs p w x ts :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_of_session h

/-- Traced sessions are closed under host-free Core runs (no tags). -/
theorem TSession.of_core_steps {p : Phase} {c c' : Config Nat} {q : L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs p false (c, q) ts)
    (hs : Steps P (fun _ _ _ _ => False) c c') :
    TSession P L m memAddr R c₀ q₀ addrs p false (c', q) ts := by
  induction hs with
  | refl => exact h
  | tail _ st ih => exact .internal ih st

/-- Every output tag is the `callOut` of a callout at a configuration of a session. -/
theorem TSession.exists_of_out {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} {b : O} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts)
    (hb : Tag.out b ∈ ts) :
    ∃ (b' : Bool) (c : Config Nat) (q : L.S) (o : Callout), Session P L c₀ q₀ addrs b' (c, q) ∧
      CalloutOf m memAddr c o ∧ R.callOut o = some b :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_of_out h hb

/-- Every input tag is the `callIn` of a callout at a configuration of a session, or the
`answerIn` of an answer to it. -/
theorem TSession.exists_of_inp {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} {i : I} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts)
    (hi : Tag.inp i ∈ ts) :
    ∃ (b' : Bool) (c : Config Nat) (q : L.S) (o : Callout), Session P L c₀ q₀ addrs b' (c, q) ∧
      CalloutOf m memAddr c o ∧ (R.callIn o = some i ∨ ∃ w, R.answerIn o w = some i) :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_of_inp h hi

/-! ## Scope facts -/

/-- **No reentrancy**: traced sessions are flat; `enter` and `exit` alternate, and the trace
ends inside an invocation exactly in phase `run`. -/
theorem TSession.openScan_eq {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    openScan false ts = some (decide (p = .run)) :=
  Silmaril.Proofs.Wasm.Game.IOAccept.openScan_eq h

/-- Nothing is entered during instantiation. -/
theorem TSession.no_enter_of_inst {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs .inst w x ts)
    (y : Option X) : Tag.enter y ∉ ts :=
  Silmaril.Proofs.Wasm.Game.IOAccept.no_enter_of_inst h rfl y

/-- **Instantiation-phase tags are internal outputs outside any invocation**: a traced session
is a prefix without `enter` (instantiation), dropped by the scope assignment, then the tags
from the first invocation on (none while still instantiating). -/
theorem TSession.bracket_eq {p : Phase} {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    ∃ pre post, ts = pre ++ post ∧ (∀ y, Tag.enter y ∉ pre) ∧
      bracket ts = assign [] pre.length post ∧ (p = .inst → post = []) :=
  Silmaril.Proofs.Wasm.Game.IOAccept.bracket_eq h

/-- During instantiation no event is scoped. -/
theorem TSession.bracket_eq_nil_of_inst {w : Bool} {x : Config Nat × L.S}
    {ts : List (Tag X I O C)} (h : TSession P L m memAddr R c₀ q₀ addrs .inst w x ts) :
    bracket ts = [] := by
  obtain ⟨pre, post, -, -, hb, hp⟩ := h.bracket_eq
  rw [hb, hp rfl, assign]

end Session

/-! ## Modules -/

variable {P : Profile} {Envs Envs' : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}
  {R : Roles X I O C}

/-- The callouts of a module are those reachable in its traced sessions. -/
theorem callouts_eq_traced :
    Callouts P Envs memIdx m = {o | ∃ (mt : CModuleType) (Is : ScalarInstance) (c₀ : Config Nat),
      IsSpecInstance m mt Is c₀ ∧ ∃ (L : SEnv UImp) (q₀ : L.S), Envs Is.store L ∧
      ∃ (p : Phase) (w : Bool) (c : Config Nat) (q : L.S) (ts : List (Tag X I O C)),
        TSession P L m c₀.frame.module.mems[memIdx]? R c₀ q₀ Is.addrs p w (c, q) ts ∧
        CalloutOf m c₀.frame.module.mems[memIdx]? c o} :=
  Silmaril.Proofs.Wasm.Game.IOAccept.callouts_eq_traced

/-- **Outputs of input-window runs are reachable callouts.** -/
theorem exists_callout_of_mem_ioRuns {r : Run I O C} {b : O}
    (hr : r ∈ ioRuns P Envs memIdx m R) (hb : b ∈ r.outputs) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_callout_of_mem_ioRuns hr hb

/-- **Outputs of entry runs are reachable callouts.** -/
theorem exists_callout_of_mem_entryIORuns {r : Run X O C} {b : O}
    (hr : r ∈ entryIORuns P Envs memIdx m R) (hb : b ∈ r.outputs) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_callout_of_mem_entryIORuns hr hb

/-- The input of an input-window run is read off a reachable callout (its arguments, or the
host's answer to it). -/
theorem exists_callout_of_input_ioRuns {r : Run I O C} (hr : r ∈ ioRuns P Envs memIdx m R) :
    ∃ o ∈ Callouts P Envs memIdx m,
      R.callIn o = some r.input ∨ ∃ w, R.answerIn o w = some r.input :=
  Silmaril.Proofs.Wasm.Game.IOAccept.exists_callout_of_input_ioRuns hr

/-- Every triggered output is the `callOut` of a reachable callout. -/
theorem exists_callout_of_mem_triggers {a : I} {b : O}
    (h : (a, b) ∈ triggers (ioRuns P Envs memIdx m R)) :
    ∃ o ∈ Callouts P Envs memIdx m, R.callOut o = some b :=
  let ⟨_, hr, _, hb⟩ := h; exists_callout_of_mem_ioRuns hr hb

/-- **Traced acceptance refines `accepted`**: with the output role `outputVia imp dec`, every
output triggered by an input is accepted by `dec` through `imp`. -/
theorem mem_accepted_of_mem_triggers {α : Type} {imp : String × String}
    {dec : Callout → Option α} {R : Roles X I α C} (hR : R.callOut = outputVia imp dec) {a : I}
    {b : α} (h : (a, b) ∈ triggers (ioRuns P Envs memIdx m R)) :
    b ∈ accepted dec P Envs memIdx imp m :=
  let ⟨o, ho, hob⟩ := exists_callout_of_mem_triggers h
  ⟨o, ho, (outputVia_eq_some_iff.1 (hR ▸ hob)).1, (outputVia_eq_some_iff.1 (hR ▸ hob)).2⟩

/-- The same for the entry reading: an output triggered by an export invocation is accepted. -/
theorem mem_accepted_of_mem_entryTriggers {α : Type} {imp : String × String}
    {dec : Callout → Option α} {R : Roles X I α C} (hR : R.callOut = outputVia imp dec) {a : X}
    {b : α} (h : (a, b) ∈ triggers (entryIORuns P Envs memIdx m R)) :
    b ∈ accepted dec P Envs memIdx imp m :=
  let ⟨_, hr, _, hb⟩ := h; let ⟨o, ho, hob⟩ := exists_callout_of_mem_entryIORuns hr hb
  ⟨o, ho, (outputVia_eq_some_iff.1 (hR ▸ hob)).1, (outputVia_eq_some_iff.1 (hR ▸ hob)).2⟩

/-! ## Monotonicity -/

/-- More admitted environments, more traces. -/
theorem tagTraces_mono (h : ∀ s L, Envs s L → Envs' s L) :
    tagTraces P Envs memIdx m R ⊆ tagTraces P Envs' memIdx m R :=
  fun _ ⟨mt, Is, c₀, hI, L, q₀, hL, rest⟩ => ⟨mt, Is, c₀, hI, L, q₀, h _ _ hL, rest⟩

/-- More admitted environments, more input-window runs (hence larger `triggers`, `episodes`,
`retTriggers`, `returns`, by their monotonicity). -/
theorem ioRuns_mono (h : ∀ s L, Envs s L → Envs' s L) :
    ioRuns P Envs memIdx m R ⊆ ioRuns P Envs' memIdx m R :=
  inputRunsOf_mono (Set.image_mono (tagTraces_mono h))

/-- More admitted environments, more entry runs. -/
theorem entryIORuns_mono (h : ∀ s L, Envs s L → Envs' s L) :
    entryIORuns P Envs memIdx m R ⊆ entryIORuns P Envs' memIdx m R :=
  entryRunsOf_mono (Set.image_mono (tagTraces_mono h))

end Silmaril.Wasm.Game.IOAccept
