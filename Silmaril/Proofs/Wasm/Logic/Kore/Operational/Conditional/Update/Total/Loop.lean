module

public import Silmaril.Proofs.Wasm.Logic.Kore.Operational.Conditional.Update.Total.Progress
public import Silmaril.Wasm.Binaryen.ConstBranchSim

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Binaryen Silmaril.Wasm.SingleThreaded
open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeAllPath

variable {H : Type} {P : Profile}

abbrev zeroLabel : LabelIdx := ⟨⟨0, by decide⟩⟩
abbrev loopBody : Instr := .loop .empty [.br zeroLabel]
def loopEntry (s : Store H) (f : Frame) : Core.Config H := ⟨s, f, [.plain loopBody]⟩
def loopLabel (s : Store H) (f : Frame) : Core.Config H :=
  ⟨s, f, [.label 0 [loopBody] [.plain (.br zeroLabel)]]⟩

-- Same profile-independent family-shape exclusion as the pinned public
-- SingleThreaded.HeadInversion, applied to loop rather than block.
local macro "not_control_family" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

private theorem loop_head {s : Store H} {f : Frame} {args : List Val} {c : Core.Config H}
    (h : Det.Head P s f args (.plain loopBody) c) :
    args = [] ∧ c = loopLabel s f := by
  cases h with
  | loop types count =>
    change some ([], []) = some (_, _) at types
    cases types
    have empty : args = [] := List.eq_nil_of_length_eq_zero count
    subst args
    exact ⟨rfl, rfl⟩
  | _ => not_control_family

/-- The actual loop instruction has only its actual label-entry successor. -/
theorem loop_entry_unique (host : HostSemantics H) (s : Store H) (f : Frame)
    {c : Core.Config H} (step : Core.Step P host (loopEntry s f) c) : c = loopLabel s f := by
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv (W := []) (i := loopBody) (rest := [])
      rfl (by simp) rfl step
  obtain ⟨rfl, rfl⟩ := loop_head head
  have empty : pre = [] := by simpa using split.symm
  subst pre
  simpa [vals] using result

private theorem bare_br_stuck (host : HostSemantics H) (s : Store H) (f : Frame)
    {c : Core.Config H} (step : Core.Step P host ⟨s, f, [.plain (.br zeroLabel)]⟩ c) : False := by
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv (W := []) (i := .br zeroLabel) (rest := [])
      rfl (by simp) rfl step
  exact ConstBranch.head_br head

/-- A label around br-zero can only jump back to the real loop instruction.
Inverting the actual LabelRed excludes inner steps and all other exits. -/
theorem loop_label_unique (host : HostSemantics H) (s : Store H) (f : Frame)
    {c : Core.Config H} (step : Core.Step P host (loopLabel s f) c) : c = loopEntry s f := by
  rcases c with ⟨s', f', code⟩
  have aligned : Core.Step P host
      ⟨s, f, vals [] ++ [.label 0 [loopBody] [.plain (.br zeroLabel)]]⟩ ⟨s', f', code⟩ := step
  obtain ⟨output, red, result⟩ := Closure.Step.label_inv aligned
  have reduced : s' = s ∧ f' = f ∧ output = [.plain loopBody] := by
    generalize bodyEq : ([.plain (.br zeroLabel)] : List Admin) = body at red
    cases red with
    | ctxt inner =>
      subst body
      exact (bare_br_stuck host s f inner).elim
    | values values =>
      have member : Admin.plain (.br zeroLabel) ∈ vals values :=
        bodyEq ▸ List.mem_singleton_self _
      exact (Det.mem_vals member rfl).elim
    | @brZero vs' vs l rest _ count =>
      have empty : vs = [] := List.eq_nil_of_length_eq_zero count
      subst vs
      exact ⟨rfl, rfl, rfl⟩
    | @brSucc vs l rest positive =>
      have peel := ConstBranch.exit_br (vs := []) (us := vs) (.br l)
        (by simpa using bodyEq)
      have labelEq : l = zeroLabel := by simpa using peel.2.1
      subst l
      have notPositive : ¬ 0 < zeroLabel.toNat := by decide
      exact (notPositive positive).elim
    | @returnCallRef vs c rest hc =>
      have peel := ConstBranch.exit_br (vs := []) (us := vs) (.returnCallRef hc)
        (by simpa using bodyEq)
      have ceq : c = .plain (.br zeroLabel) := by simpa using peel.2.1
      rw [ceq] at hc
      simp [Admin.IsReturnCallRef] at hc
    | @return_ vs rest =>
      have peel := ConstBranch.exit_br (vs := []) (us := vs) .return_
        (by simpa using bodyEq)
      simp at peel
    | throwRef a => simp [throwing] at bodyEq
    | trap => simp at bodyEq
  change (⟨s', f', code⟩ : Core.Config H) = ⟨s, f, [.plain loopBody]⟩
  simp only [Core.Config.mk.injEq]
  refine ⟨reduced.1, reduced.2.1, ?_⟩
  simpa only [vals, List.map_nil, List.nil_append, reduced.2.2] using result

/-- A serial invariant excludes every finite complete path, independently of
whether an infinite path has already been chosen. -/
private theorem allPartial_false_of_serial_invariant {W : Type} (R : W → W → Prop)
    (I : W → Prop) (closed : ∀ a b, I a → R a b → I b)
    (serial : ∀ a, I a → ∃ b, R a b) (a : W) (initial : I a) :
    Silmaril.Logic.Reachability.AllPartial R (fun _ => False) a := by
  intro n path start edges terminal
  have inv : ∀ i, i ≤ n → I (path i) := by
    intro i
    induction i with
    | zero => intro _; exact start.symm ▸ initial
    | succ i ih =>
      intro bound
      exact closed _ _ (ih (Nat.le_of_succ_le bound))
        (edges i (Nat.lt_of_succ_le bound))
  obtain ⟨next, step⟩ := serial _ (inv n le_rfl)
  exact (terminal next step).elim

/-- For the real native loop, finite-complete-path partial correctness with an
impossible target is vacuous. This is NOT strong AF False. -/
theorem loop_allPartial_false (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) :
    Silmaril.Logic.Reachability.AllPartial (Core.Step P host) (fun _ => False) (loopEntry s f) := by
  have enter : Core.Step P host (loopEntry s f) (loopLabel s f) := by
    simpa [loopEntry, loopLabel, loopBody, vals, expression] using
      (Core.Step.loop (P := P) (host := host) (s := s) (f := f)
        (bt := .empty) (body := [.br zeroLabel]) (vs := []) rfl rfl)
  have back : Core.Step P host (loopLabel s f) (loopEntry s f) := by
    simpa [loopEntry, loopLabel, loopBody, vals, expression] using
      (Core.Step.brLabelZero (P := P) (host := host) (s := s) (f := f)
        (n := 0) (cont := [loopBody]) (vs' := []) (vs := []) (l := zeroLabel)
        (rest := []) rfl rfl)
  apply allPartial_false_of_serial_invariant (Core.Step P host)
    (fun c => c = loopEntry s f ∨ c = loopLabel s f) ?_ ?_ _ (Or.inl rfl)
  · intro a b ha step
    rcases ha with rfl | rfl
    · exact Or.inr (loop_entry_unique host s f step)
    · exact Or.inl (loop_label_unique host s f step)
  · intro a ha
    rcases ha with rfl | rfl
    · exact ⟨_, enter⟩
    · exact ⟨_, back⟩

/-- Same actual relation, state and impossible target: partial all-path truth
coexists with failure of strong AF because the native infinite trace avoids it. -/
theorem loop_separates_partial_from_total (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) :
    Silmaril.Logic.Reachability.AllPartial (Core.Step P host) (fun _ => False) (loopEntry s f) ∧
      ¬ Silmaril.Logic.CTL.Sat (predicateModel P host (loopEntry s f) (fun _ => False))
        eventuallyTarget :=
  ⟨loop_allPartial_false P host s f,
    fun af => loop_not_allEventually P host s f ((af_iff_allEventually P host _ _).mp af)⟩

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
