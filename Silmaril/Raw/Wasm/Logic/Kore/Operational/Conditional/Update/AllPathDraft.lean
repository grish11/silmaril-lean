module

public import Silmaril.Raw.Wasm.Logic.Kore.Operational.Conditional.Update.CheckedUpdateDraft
public import Silmaril.Logic.Reachability.AllPath.Thms
public import Silmaril.Wasm.Binaryen.GrowOOMRun
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro

/-! Native prefix inversion for the checked authored counter-update compiler.
The existing parser, source fixtures and finite simulation remain unchanged. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeAllPath
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Binaryen
open Silmaril.Wasm.SingleThreaded
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
open GrowWrapper (Forced)
open Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Native

variable {H : Type} {P : Profile}

/-- An actual host-free successor excludes a simultaneous host-call redex.
Only the current configuration matters; later host behaviour is unrestricted. -/
theorem hostFree_of_active {a b c : Core.Config H} (active : Core.Step P closedHost a b)
    (host : HostSemantics H) (step : Core.Step P host a c) : Core.Step P closedHost a c := by
  rcases SingleThreaded.Step.split_host step with h | ⟨E, address, function, args, redex, _⟩
  · exact h
  · have noRedex := decompose?_none_of_noRedex (SingleThreaded.Step.noRedex active)
    rw [noRedex] at redex
    cases redex

/-- Every finite complete path hits the endpoint of a forced prefix. No global
profile/host determinism or assumption about the later continuation is used. -/
theorem forced_allPartial {a b : Core.Config H} (forcedRun : Forced (P := P) a b)
    (host : HostSemantics H) (Q : Core.Config H → Prop) (post : Q b) :
    Silmaril.Logic.Reachability.AllPartial (Core.Step P host) Q a := by
  induction forcedRun with
  | done a =>
      intro n path start _ _
      exact ⟨0, Nat.zero_le _, start.symm ▸ post⟩
  | @step a b c active unique tail ih =>
      intro n path start edges terminal
      cases n with
      | zero => exact (terminal b (start.symm ▸ active.of_noHost host)).elim
      | succ n =>
          have first : Core.Step P host a (path 1) := start ▸ edges 0 (Nat.zero_lt_succ n)
          have forced : path 1 = b := unique _ (hostFree_of_active active host first)
          have tailEdges : ∀ i, i < n → Core.Step P host (path (i+1)) (path ((i+1)+1)) := by
            intro i hi
            exact edges (i+1) (Nat.succ_lt_succ hi)
          obtain ⟨i, hi, hit⟩ := ih post n (fun i => path (i+1)) forced tailEdges terminal
          exact ⟨i+1, Nat.succ_le_succ hi, hit⟩

/-- An initialized active local read has exactly its operational successor,
with arbitrary older operands and administrative continuation. -/
theorem localGet_unique {s : Store H} {f : Frame} {older : List Val}
    {x : LocalIdx} {v : Val} {rest : List Admin} {c : Core.Config H}
    (read : f.local? x = some (some v))
    (h : Core.Step P closedHost ⟨s, f, vals older ++ .plain (.localGet x) :: rest⟩ c) :
    c = ⟨s, f, vals older ++ v.toAdmin :: rest⟩ := by
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv rfl (by simp) rfl h
  obtain ⟨rfl, value, lookup, rfl⟩ := GuardSim.head_localGet head
  have eq : value = v := by simpa [read] using lookup.symm
  subst value
  simpa [split] using result

/-- Branch selection consumes precisely its i32 condition. -/
theorem if_unique {s : Store H} {f : Frame} {older : List Val}
    {q : BitVec 32} {bt : BlockType} {yes no : List Instr} {rest : List Admin}
    {c : Core.Config H}
    (h : Core.Step P closedHost
      ⟨s, f, vals older ++ [constI32 q, .plain (.if_ bt yes no)] ++ rest⟩ c) :
    c = ⟨s, f, vals older ++ .plain (.block bt (if q = 0 then no else yes)) :: rest⟩ := by
  have h' : Core.Step P closedHost
      ⟨s, f, vals (older ++ [Val.i32 q]) ++ .plain (.if_ bt yes no) :: rest⟩ c := by
    simpa [vals, Val.i32, Val.toAdmin, constI32, List.append_assoc] using h
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv rfl (by simp) rfl h'
  obtain ⟨value, rfl, rfl⟩ := GuardSim.head_if head
  obtain ⟨rfl, valueEq⟩ := Det.append_singleton_inj.mp split
  have eq : q = value := by cases valueEq; rfl
  subst value
  simpa using result

/-- The structural empty block type consumes no older operand. -/
theorem block_unique {s : Store H} {f : Frame} {older : List Val}
    {bt : BlockType} {body : List Instr} {rest : List Admin} {c : Core.Config H}
    (blockType : f.module.blockType? bt = some ([], []))
    (h : Core.Step P closedHost ⟨s, f, vals older ++ .plain (.block bt body) :: rest⟩ c) :
    c = ⟨s, f, vals older ++ .label 0 [] (expression body) :: rest⟩ := by
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv rfl (by simp) rfl h
  obtain ⟨input, output, types, count, rfl⟩ := SingleThreaded.head_block head
  rw [blockType] at types
  cases types
  have empty : args = [] := List.eq_nil_of_length_eq_zero count
  subst args
  simpa [split] using result

/-- A live body can only advance inside its label; this excludes every label
exit by operational inversion, before the body has finished. -/
theorem label_context_unique {s t : Store H} {f g : Frame}
    {body next : List Admin} {n : Nat} {cont : List Instr}
    (active : Core.Step P closedHost ⟨s, f, body⟩ ⟨t, g, next⟩)
    (unique : ∀ c, Core.Step P closedHost ⟨s, f, body⟩ c → c = ⟨t, g, next⟩)
    {older : List Val} {rest : List Admin} {c : Core.Config H}
    (h : Core.Step P closedHost ⟨s, f, vals older ++ .label n cont body :: rest⟩ c) :
    c = ⟨t, g, vals older ++ .label n cont next :: rest⟩ := by
  rcases c with ⟨s', f', code⟩
  rcases Core.Sim.Step.split_head (vs := older) rfl h with
    ⟨pre, args, out, split, step, result⟩ | ⟨impossible, _⟩ | ⟨impossible, _⟩
  · obtain ⟨output, red, codeEq⟩ := Closure.Step.label_inv step
    obtain ⟨inner, innerStep, innerEq⟩ := CoalesceLocalsLite.labelRed_ctxt_of_step active red
    have forced := unique _ innerStep
    simp only [Core.Config.mk.injEq] at forced
    simp only [Core.Config.mk.injEq]
    refine ⟨forced.1, forced.2.1, ?_⟩
    rw [result, codeEq, innerEq, forced.2.2]
    simp [split, vals, List.append_assoc]
  · cases impossible
  · cases impossible

/-- Finished empty labels consume no older value and preserve the continuation. -/
theorem label_empty_unique {s : Store H} {f : Frame} {older : List Val}
    {n : Nat} {cont : List Instr} {rest : List Admin} {c : Core.Config H}
    (h : Core.Step P closedHost ⟨s, f, vals older ++ .label n cont [] :: rest⟩ c) :
    c = ⟨s, f, vals older ++ rest⟩ := by
  rcases c with ⟨s', f', code⟩
  rcases Core.Sim.Step.split_head (vs := older) rfl h with
    ⟨pre, args, out, split, step, result⟩ | ⟨impossible, _⟩ | ⟨impossible, _⟩
  · obtain ⟨output, red, codeEq⟩ := Closure.Step.label_inv step
    have finished : s' = s ∧ f' = f ∧ output = [] := by
      generalize empty : ([] : List Admin) = body at red
      cases red with
      | ctxt inner =>
          subst body
          exact False.elim (Core.Step.not_vals (P := P) (host := closedHost)
            (s := s) (f := f) (vs := []) inner)
      | values values =>
          have nil : values = [] := by
            have count := congrArg List.length empty
            simpa [vals] using count.symm
          subst values
          exact ⟨rfl, rfl, rfl⟩
      | brZero | brSucc | returnCallRef | return_ | throwRef | trap =>
          simp [vals, throwing] at empty
    simp only [Core.Config.mk.injEq]
    refine ⟨finished.1, finished.2.1, ?_⟩
    rw [result, codeEq, finished.2.2]
    simp [split, vals, List.append_assoc]
  · cases impossible
  · cases impossible

/-- Literal assignment executes through its real frame update and label exit.
Every native successor is forced, uniformly in the surrounding stack and code. -/
theorem block_assign_forced (s : Store H) (f : Frame) (older : List Val)
    (rest : List Admin) (bt : BlockType) (target : LocalIdx) (value : BitVec 32)
    (blockType : f.module.blockType? bt = some ([], []))
    (bound : target.toNat < f.locals.length) :
    Forced (P := P)
      ⟨s, f, vals older ++ .plain (.block bt (BodyDraft.assignBody target value)) :: rest⟩
      ⟨s, f.setLocal target (Val.i32 value), vals older ++ rest⟩ := by
  have enter : Core.Step P closedHost
      ⟨s, f, [.plain (.block bt (BodyDraft.assignBody target value))]⟩
      ⟨s, f, [.label 0 [] (expression (BodyDraft.assignBody target value))]⟩ := by
    simpa only [vals, List.map_nil, List.nil_append, List.length_nil] using
      (Core.Step.block (P := P) (host := closedHost) (s := s) (f := f)
        (body := BodyDraft.assignBody target value) (vs := []) blockType rfl)
  refine Forced.step (by simpa only [List.singleton_append, List.append_assoc] using
    (Core.Sim.Step.append_right (Core.Sim.Step.vals_left enter older) rest))
    (fun _ h => block_unique blockType h) ?_
  have write : Core.Step P closedHost
      ⟨s, f, expression (BodyDraft.assignBody target value)⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩ :=
    by
      change Core.Step P closedHost
        ⟨s, f, [(Val.i32 value).toAdmin, .plain (.localSet target)]⟩ _
      exact Core.Step.variable (Core.VariableStep.localSet bound)
  have write_unique : ∀ c, Core.Step P closedHost
      ⟨s, f, expression (BodyDraft.assignBody target value)⟩ c →
      c = ⟨s, f.setLocal target (Val.i32 value), []⟩ := by
    intro c h
    simpa only [vals, List.map_nil, List.nil_append] using
      (SimplifyLocalsLite.localSet_step_unique (vs := []) h)
  refine Forced.step (by simpa only [List.singleton_append, List.append_assoc] using
    (Core.Sim.Step.append_right (Core.Sim.Step.vals_left (Core.Step.ctxtLabel write) older) rest))
    (fun _ h => label_context_unique write write_unique h) ?_
  have leave : Core.Step P closedHost
      ⟨s, f.setLocal target (Val.i32 value), [.label 0 [] []]⟩
      ⟨s, f.setLocal target (Val.i32 value), []⟩ :=
    Core.Step.labelVals (vs := [])
  exact Forced.step (by simpa only [List.singleton_append, List.append_assoc,
    List.append_nil, List.nil_append] using
    (Core.Sim.Step.append_right (Core.Sim.Step.vals_left leave older) rest))
    (fun _ h => label_empty_unique h) (Forced.done _)

/-- Generic initialized native prefix: read the condition, select its branch,
execute the chosen assignment, and retain the exact continuation. -/
theorem entry_forced (L : Layout) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal target : LocalIdx) (q zeroValue nonzeroValue : BitVec 32)
    (read : f.local? valueLocal = some (some (Val.i32 q)))
    (zeroBody : L.zeroBody = BodyDraft.assignBody target zeroValue)
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody target nonzeroValue)
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (bound : target.toNat < f.locals.length) :
    Forced (P := P) (native L .entry s f older tail rest valueLocal)
      ⟨s, f.setLocal target (Val.i32 (if q = 0 then zeroValue else nonzeroValue)),
        vals older ++ L.tailCode tail ++ rest⟩ := by
  have get : Core.Step P closedHost ⟨s, f, [.plain (.localGet valueLocal)]⟩
      ⟨s, f, [constI32 q]⟩ := Core.Step.variable (Core.VariableStep.localGet read)
  refine Forced.step (d := ⟨s, f, vals older ++
      [constI32 q, .plain (.if_ L.blockType L.nonzeroBody L.zeroBody)] ++ L.tailCode tail ++ rest⟩)
    (by simpa [native, List.append_assoc] using
      (Core.Sim.Step.append_right (Core.Sim.Step.vals_left get older)
        (.plain (.if_ L.blockType L.nonzeroBody L.zeroBody) :: (L.tailCode tail ++ rest))))
    (fun _ h => by
      simpa [List.append_assoc, constI32, Val.toAdmin] using
        (localGet_unique (P := P) (older := older)
          (rest := .plain (.if_ L.blockType L.nonzeroBody L.zeroBody) :: (L.tailCode tail ++ rest)) read
          (by simpa [native, List.append_assoc] using h))) ?_
  have select : Core.Step P closedHost
      ⟨s, f, [constI32 q, .plain (.if_ L.blockType L.nonzeroBody L.zeroBody)]⟩
      ⟨s, f, [.plain (.block L.blockType (if q = 0 then L.zeroBody else L.nonzeroBody))]⟩ := by
    by_cases zero : q = 0
    · subst q; exact Core.Step.ifFalse
    · simpa only [zero, ↓reduceIte] using
        (Core.Step.ifTrue (P := P) (host := closedHost) (s := s) (f := f)
          (bt := L.blockType) (b₁ := L.nonzeroBody) (b₂ := L.zeroBody) zero)
  refine Forced.step (by simpa only [List.singleton_append, List.append_assoc] using
    (Core.Sim.Step.append_right (Core.Sim.Step.vals_left select older) (L.tailCode tail ++ rest)))
    (fun _ h => by
      simpa only [List.append_assoc] using
        (if_unique (P := P) (rest := L.tailCode tail ++ rest)
          (by simpa only [List.append_assoc] using h))) ?_
  by_cases zero : q = 0
  · simpa [zero, zeroBody, List.append_assoc] using
      block_assign_forced (P := P) s f older (L.tailCode tail ++ rest) L.blockType target
        zeroValue blockType bound
  · simpa only [zero, ↓reduceIte, nonzeroBody, List.append_assoc] using
      block_assign_forced (P := P) s f older (L.tailCode tail ++ rest) L.blockType target
        nonzeroValue blockType bound

/-- Full operational contract for the existing task: all finite complete paths
hit the actual source/native post-relation. Every hypothesis constrains initial
syntax/state; no assumed reachability or semantic validity is supplied. -/
theorem allPath (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31) :
    Task.allPath L P host s f older tail rest valueLocal counterLocal q z n := by
  have read : f.local? valueLocal = some (some (Val.i32 q)) := by
    have observed := agree.1
    unfold Silmaril.Wasm.Logic.Core.localVal? at observed
    split at observed <;> simp_all
  have forcedRun := entry_forced (P := P) L s f older tail rest valueLocal counterLocal q
    (BitVec.ofInt 32 z) (BitVec.ofInt 32 n) read zeroBody nonzeroBody blockType bound
  apply forced_allPartial forcedRun host
    (postRelated L s f older tail rest valueLocal counterLocal q z n (afterSource L tail q z n))
  have signed : (BitVec.ofInt 32 (if q = 0 then z else n)).toInt = (if q = 0 then z else n) := by
    split
    · exact signed_representation z zlo zhi
    · exact signed_representation n nlo nhi
  refine ⟨rfl, ?_, write_agrees f valueLocal counterLocal q k _ distinct bound agree, signed⟩
  rw [apply_ite (BitVec.ofInt 32)]


/-- The all-path encoding has exactly the actual finite-complete-path meaning. -/
theorem compiled_iff_allPartial (P : Profile) (host : HostSemantics H)
    (initial : Core.Config H) (Q : Core.Config H → Prop) :
    Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P host initial Q)
      (Reachability.encode () (Reachability.atomRule .allPath false true)) ↔
      Reachability.AllPartial (Core.Step P host) Q initial := by
  let _ : Nonempty (Core.Config H) := ⟨initial⟩
  rw [Reachability.encode_correct]
  change (Reachability.atomRule .allPath false true).Satisfies ()
    (Reachability.relationalModel (Core.Step P host)
      (fun flag : Bool => {c | if flag then Q c else c = initial})) ↔ _
  rw [Reachability.atomRule_iff]
  change (∀ c, c = initial → Reachability.AllPartial (Core.Step P host) Q c) ↔ _
  exact ⟨fun h => h initial rfl, fun h c hc => hc ▸ h⟩

/-- Missing initialized locals are an actual native deadlock, under every host. -/
theorem localGet_stuck (host : HostSemantics H) (s : Store H) (f : Frame)
    (older : List Val) (x : LocalIdx) (rest : List Admin)
    (missing : ∀ v, f.local? x ≠ some (some v)) :
    Task.actualStuck P host ⟨s, f, vals older ++ .plain (.localGet x) :: rest⟩ := by
  intro c h
  obtain ⟨pre, args, out, split, head, result⟩ :=
    SingleThreaded.inert_head_inv rfl (by simp) rfl h
  obtain ⟨_, v, lookup, _⟩ := GuardSim.head_localGet head
  exact missing v lookup

/-- With no initialized condition local, the unpremised task is false.
The input still contains two native instructions that the required endpoint
has consumed. This is an operational counterexample, independent of literals. -/
theorem unpremised_allPath_false (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx) (q : BitVec 32) (z n : Int)
    (missing : ∀ v, f.local? valueLocal ≠ some (some v)) :
    ¬ Task.allPath L P host s f older tail rest valueLocal counterLocal q z n := by
  have terminal : ∀ c, ¬ Core.Step P host
      (native L .entry s f older tail rest valueLocal) c := by
    simpa only [Task.actualStuck, native, List.append_assoc, List.cons_append, List.nil_append] using
      localGet_stuck (P := P) host s f older valueLocal
        (.plain (.if_ L.blockType L.nonzeroBody L.zeroBody) :: (L.tailCode tail ++ rest)) missing
  intro all
  have hit := (Reachability.allPartial_deadlock _ _ _ terminal).mp all
  have code := congrArg Core.Config.code hit.2.1
  have length := congrArg List.length code
  simp [native, vals, List.length_append] at length
  omega

/-- A native unreachable instruction really reaches the native trap. -/
theorem unreachable_actualTrap (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) :
    Task.actualTrap P host ⟨s, f, [.plain .unreachable]⟩ :=
  ⟨s, f, (Core.Step.parametric Core.ParametricStep.unreachable).steps⟩

/-- The native loop/br-zero cycle supplies an actual infinite trace. -/
theorem loop_actualDivergence (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) :
    Task.actualDivergence P host
      ⟨s, f, [.plain (.loop .empty [.br ⟨⟨0, by decide⟩⟩])]⟩ := by
  let l : LabelIdx := ⟨⟨0, by decide⟩⟩
  let body : Instr := .loop .empty [.br l]
  let a : Core.Config H := ⟨s, f, [.plain body]⟩
  let b : Core.Config H := ⟨s, f, [.label 0 [body] [.plain (.br l)]]⟩
  have enter : Core.Step P host a b := by
    simpa [a, b, body, vals, expression] using
      (Core.Step.loop (P := P) (host := host) (s := s) (f := f)
        (bt := .empty) (body := [.br l]) (vs := []) rfl rfl)
  have back : Core.Step P host b a := by
    simpa [a, b, body, vals, expression] using
      (Core.Step.brLabelZero (P := P) (host := host) (s := s) (f := f)
        (n := 0) (cont := [body]) (vs' := []) (vs := []) (l := l) (rest := []) rfl rfl)
  exact Silmaril.InfiniteTrace.coinduct (fun c => c = a ∨ c = b)
    (by intro c hc; rcases hc with rfl | rfl
        · exact ⟨b, enter, Or.inr rfl⟩
        · exact ⟨a, back, Or.inl rfl⟩)
    (Or.inl rfl)

/-- Concrete empty-frame instance refutes the task without initialization
premises, for every layout, host and literal pair. -/
theorem empty_frame_counterexample (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (valueLocal counterLocal : LocalIdx) (q : BitVec 32) (z n : Int) :
    ¬ Task.allPath L P host s ({} : Frame) [] [] [] valueLocal counterLocal q z n :=
  unpremised_allPath_false L P host s {} [] [] [] valueLocal counterLocal q z n
    (by intro v; simp [Frame.local?])

/-- Checked source-rule installation and an actual source update determine the
same after relation reached on every finite complete native path. -/
theorem checked_allPath_matching (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal counterLocal : LocalIdx)
    (q k : BitVec 32) (z n : Int)
    (distinct : valueLocal.toNat ≠ counterLocal.toNat)
    (bound : counterLocal.toNat < f.locals.length)
    (agree : LocalsAgree f valueLocal counterLocal q k)
    (zeroBody : L.zeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 z))
    (nonzeroBody : L.nonzeroBody = BodyDraft.assignBody counterLocal (BitVec.ofInt 32 n))
    (blockType : f.module.blockType? L.blockType = some ([], []))
    (zlo : -(2^31) ≤ z) (zhi : z < 2^31)
    (nlo : -(2^31) ≤ n) (nhi : n < 2^31)
    (input : String) (program : CheckedProgram)
    (_checked : check input = some program)
    (installed : program.axioms = rules L z n)
    (d : Config) (step : Step program.axioms (entrySource L tail q k) d) :
    Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P host
        (native L .entry s f older tail rest valueLocal)
        (postRelated L s f older tail rest valueLocal counterLocal q z n d))
      (Reachability.encode () (Reachability.atomRule .allPath false true)) := by
  have hd := (source_step_iff L tail q k z n d).mp (by simpa only [installed] using step)
  subst d
  exact (compiled_iff_allPartial P host _ _).mpr
    (allPath L P host s f older tail rest valueLocal counterLocal q k z n
      distinct bound agree zeroBody nonzeroBody blockType zlo zhi nlo nhi)

/-- The same actual native predicate model rejects the uninitialized compiler
entry under the all-path encoding; a stuck state is not treated as divergence. -/
theorem empty_frame_no_allPath_matching (L : Layout) (P : Profile)
    (host : HostSemantics H) (s : Store H) (valueLocal counterLocal : LocalIdx)
    (q : BitVec 32) (z n : Int) :
    ¬ Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P host
        (native L .entry s ({} : Frame) [] [] [] valueLocal)
        (postRelated L s ({} : Frame) [] [] [] valueLocal counterLocal q z n
          (afterSource L [] q z n)))
      (Reachability.encode () (Reachability.atomRule .allPath false true)) :=
  fun h => empty_frame_counterexample L P host s valueLocal counterLocal q z n
    ((compiled_iff_allPartial P host _ _).mp h)


/-- A finite native trap run is rejected by the all-path encoding with an
impossible target; this is separate from the genuine infinite loop control. -/
theorem unreachable_no_false_allPath_matching (P : Profile)
    (s : Store H) (f : Frame) :
    ¬ Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P closedHost
        ⟨s, f, [.plain .unreachable]⟩ (fun _ => False))
      (Reachability.encode () (Reachability.atomRule .allPath false true)) := by
  intro h
  have all := (compiled_iff_allPartial P closedHost _ _).mp h
  have next := all.successor (by simp)
    (Core.Step.parametric Core.ParametricStep.unreachable)
  exact (Reachability.allPartial_deadlock _ _ _
    (fun _ h => Det.not_step_trap h)).mp next

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeAllPath
