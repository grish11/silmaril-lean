module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs

open CallContinuation.OuterCall.Ranked
open Graph (Program)
open Execution.Runtime (Value)
open CallContinuation.OuterCall.Computed

abbrev Entered (a : Graph.Phase) : Prop := a.LabelOutcome ∨ ∃ result, a = .done result

private theorem after_block {a : Graph.Phase} (h : Entered a) (saved result rest kind) :
    Entered (a.afterBlock saved result rest kind) := by
  rcases h with h | ⟨_, rfl⟩
  · cases a <;> try contradiction
    all_goals first | exact .inl trivial | rename_i result; cases result <;> exact .inl trivial
  · exact .inr ⟨_, rfl⟩

private theorem layer_entered {program : Program} {fn : Graph.Function} {a b : Graph.Phase}
    {kind : Graph.LabelKind}
    (move : Graph.Layer fn (fun t => program.FrameEdge t.address) a b kind) :
    a.LabelOutcome → Entered b := by
  induction move <;> intro live
  all_goals try first
    | exact .inl trivial
    | exact .inr ⟨_, rfl⟩
    | contradiction
    | apply after_block; apply_assumption; trivial
  case branchHere kind _ _ _ _ _ _ => cases kind <;> exact .inl trivial

theorem step_entered {call : Invocation} {program : Program} (checked : call.Checked program)
    {a b : Graph.Phase} (live : a.LabelOutcome) (move : program.FrameEdge call.address a b) : Entered b :=
  layer_entered ((Program.frameEdge_iff checked.found).mp move) live

theorem not_call {a : Graph.Phase} (live : a.LabelOutcome) (args) : a ≠ .call args := by
  rintro rfl
  exact live

theorem entered_admitted {call : Invocation} {program : Program} (checked : call.Checked program) :
    Graph.Admitted program call.callee call.entered :=
  Graph.Program.frame_admitted_step checked.graph checked.found
    (.invoke (by simpa only [← resolved_signature checked.resolved checked.found, CallContinuation.OuterCall.Declaration.type] using checked.typed))
    (resolved_frame_entry checked.resolved checked.found checked.typed)

private theorem lift_runs {A C : Type} {edge : A → A → Prop} {native : C → C → Prop}
    (valid : A → Prop) (render : A → C)
    (preserve : ∀ {a b}, valid a → edge a b → valid b)
    (step : ∀ {a b}, valid a → (native (render a) b ↔ ∃ out, edge a out ∧ b = render out))
    {a : A} {b : C} (ready : valid a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, Relation.ReflTransGen edge a out ∧ valid out ∧ b = render out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ h ih =>
      obtain ⟨phase, run, validPhase, rfl⟩ := ih
      obtain ⟨out, move, rfl⟩ := (step validPhase).mp h
      exact ⟨out, run.tail move, preserve validPhase move, rfl⟩
  · rintro ⟨out, path, validOut, rfl⟩
    clear validOut
    suffices Relation.ReflTransGen native (render a) (render out) ∧ valid out from this.1
    induction path with
    | refl => exact ⟨.refl, ready⟩
    | tail _ h ih =>
      obtain ⟨run, validPhase⟩ := ih
      exact ⟨run.tail ((step validPhase).mpr ⟨_, h, rfl⟩), preserve validPhase h⟩

theorem frame_runs_iff {C : Type} {call : Invocation} {program : Program} (checked : call.Checked program)
    (render : Graph.Phase → C) (native : C → C → Prop)
    (step : ∀ {a b}, Graph.Admitted program call.callee a → a.LabelOutcome →
      (native (render a) b ↔ ∃ out, program.FrameEdge call.address a out ∧ b = render out))
    (stopped : ∀ result b, ¬ native (render (.done result)) b)
    {b : C} :
    Relation.ReflTransGen native (render call.entered) b ↔
      ∃ out, program.FrameRuns call.address call.entered out ∧
        Graph.Admitted program call.callee out ∧ Entered out ∧ b = render out := by
  have preserve {a b} (h : Graph.Admitted program call.callee a ∧ Entered a)
      (move : program.FrameEdge call.address a b) :
      Graph.Admitted program call.callee b ∧ Entered b := by
    refine ⟨Graph.Program.frame_admitted_step checked.graph checked.found h.1 move, ?_⟩
    rcases h.2 with live | ⟨result, rfl⟩
    · exact step_entered checked live move
    · cases (Program.frameEdge_iff checked.found).mp move
  have one {a b} (h : Graph.Admitted program call.callee a ∧ Entered a) :
      native (render a) b ↔ ∃ out, program.FrameEdge call.address a out ∧ b = render out := by
    rcases h.2 with live | ⟨result, rfl⟩
    · exact step h.1 live
    · exact iff_of_false (stopped result b) (by
        rintro ⟨_, move, _⟩
        cases (Program.frameEdge_iff checked.found).mp move)
  have ready : Graph.Admitted program call.callee call.entered ∧ Entered call.entered :=
    ⟨entered_admitted checked, .inl trivial⟩
  simpa only [and_assoc] using (lift_runs (edge := program.FrameEdge call.address) (native := native)
      (fun a => Graph.Admitted program call.callee a ∧ Entered a) render (fun h e => preserve h e)
      (fun h => one h) ready)

theorem trap_runs_iff {A C : Type} (render : List Value → List A → C) (native : C → C → Prop)
    (step : ∀ {saved rest b}, native (render saved rest) b ↔
      ∃ kept remaining, Prefix.Discard saved rest kept remaining ∧ b = render kept remaining)
    {saved : List Value} {rest : List A} {b : C} :
    Relation.ReflTransGen native (render saved rest) b ↔
      ∃ kept remaining, Relation.ReflTransGen
        (fun (a b : List Value × List A) => Prefix.Discard a.1 a.2 b.1 b.2)
        (saved, rest) (kept, remaining) ∧ b = render kept remaining := by
  have one {a : List Value × List A} {b} (_ : True) := step (saved := a.1) (rest := a.2) (b := b)
  simpa only [true_and, Prod.exists] using
    (lift_runs (fun _ => True) (fun (a : List Value × List A) => render a.1 a.2)
      (fun _ _ => trivial) (fun h => (one h).trans (by simp only [Prod.exists]))
      (a := (saved, rest)) (b := b) trivial)

theorem run_iff {A C : Type} {call : Invocation} {program : Program}
    {rest : List A} {entryTrace : List C} {render : Graph.Phase → C} {trap : List Value → List A → C}
    {native frameStep : C → C → Prop} {out : C}
    (chain : entryTrace.IsChain (fun a b => ∀ dst, native a dst ↔ dst = b))
    (frame : ∀ {b}, Relation.ReflTransGen frameStep (render call.entered) b ↔
      ∃ phase, program.FrameRuns call.address call.entered phase ∧
        Graph.Admitted program call.callee phase ∧ Entered phase ∧ b = render phase)
    (trapRun : ∀ {b}, Relation.ReflTransGen native (trap call.saved rest) b ↔
      ∃ kept remaining, Relation.ReflTransGen
        (fun (a b : List Value × List A) => Prefix.Discard a.1 a.2 b.1 b.2)
        (call.saved, rest) (kept, remaining) ∧ b = trap kept remaining)
    (trap_eq : ∀ phase, Entered phase → (trap call.saved rest = render phase ↔ phase = .done .trap))
    (tracked : ∀ phase, program.FrameRuns call.address call.entered phase →
      Graph.Admitted program call.callee phase ∧ Entered phase) :
    NativeRun native frameStep entryTrace (render call.entered) (trap call.saved rest) out ↔
      call.Run program rest entryTrace render trap out := by
  have trapFrame : Relation.ReflTransGen frameStep (render call.entered) (trap call.saved rest) ↔
      program.FrameRuns call.address call.entered (.done .trap) := by
    constructor
    · intro run
      obtain ⟨phase, path, _, live, eq⟩ := frame.mp run
      exact (trap_eq phase live).mp eq ▸ path
    · intro run
      have h := tracked _ run
      exact frame.mpr ⟨_, run, h.1, h.2, (trap_eq _ h.2).mpr rfl⟩
  have frameOut : Relation.ReflTransGen frameStep (render call.entered) out ↔
      ∃ phase, program.FrameRuns call.address call.entered phase ∧
        Graph.Admitted program call.callee phase ∧ out = render phase :=
    frame.trans ⟨fun ⟨phase, run, admitted, _, eq⟩ => ⟨phase, run, admitted, eq⟩,
      fun ⟨phase, run, admitted, eq⟩ => ⟨phase, run, admitted, (tracked phase run).2, eq⟩⟩
  simp only [NativeRun, Invocation.Run, frameOut, trapFrame, trapRun, chain, true_and]

theorem tracked {call : Invocation} {program : Program} (checked : call.Checked program)
    (phase : Graph.Phase) (run : program.FrameRuns call.address call.entered phase) :
    Graph.Admitted program call.callee phase ∧ Entered phase := by
  refine ⟨program.frame_admitted_run checked.graph checked.found (entered_admitted checked) run, ?_⟩
  induction run with
  | refl => exact .inl trivial
  | tail _ move ih =>
    rcases ih with live | ⟨result, rfl⟩
    · exact step_entered checked live move
    · cases (Program.frameEdge_iff checked.found).mp move

theorem map_ne_singleton {A B : Type} (emit : A → B) (values : List A) (x : B)
    (notEq : ∀ a, emit a ≠ x) : values.map emit ≠ [x] := by
  cases values with
  | nil => simp
  | cons a rest => simp [notEq a]

theorem chain_member {C : Type} {native : C → C → Prop} {start out : C} {rest : List C}
    (chain : (start :: rest).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b))
    (member : out ∈ start :: rest) : Relation.ReflTransGen native start out := by
  induction rest generalizing start with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    exact .refl
  | cons mid rest ih =>
    rcases List.mem_cons.mp member with rfl | next
    · exact .refl
    · obtain ⟨one, chain⟩ := List.isChain_cons_cons.mp chain
      exact (ih chain next).head ((one mid).mpr rfl)

theorem native_steps {C : Type} {native frameStep : C → C → Prop}
    {start entered trapped out : C} {rest : List C}
    (entry : entered ∈ start :: rest) (underFrame : ∀ {a b}, frameStep a b → native a b)
    (run : NativeRun native frameStep (start :: rest) entered trapped out) :
    Relation.ReflTransGen native start out := by
  have lift {b} (path : Relation.ReflTransGen frameStep entered b) :
      Relation.ReflTransGen native entered b := by
    induction path with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (underFrame step)
  obtain ⟨chain, runs⟩ := run
  rcases runs with mem | frame | ⟨frame, trap⟩
  · exact chain_member chain mem
  · exact (chain_member chain entry).trans (lift frame)
  · exact ((chain_member chain entry).trans (lift frame)).trans trap

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs
