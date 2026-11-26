module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.MLIR.SCF (For)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run lower_returns_iff)

variable {Input Γ Δ args : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {tree : DominatorTree (lower g)}
variable {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

private theorem evalCapture (operands : Operands (carried :: Input) args)
    {captured : Operands Input args} (found : capture? operands = some captured)
    (input : Env Input) (old : BitVec carried.val) :
    operands.eval (.cons old input) = captured.eval input := by
  induction operands with
  | nil =>
    cases found
    rfl
  | cons head rest ih =>
    cases head with
    | here => cases found
    | there ref =>
      obtain ⟨tail, translated, rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [Operands.eval, Env.get, ih translated]

private theorem evalRename (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (operands : Operands Γ args) :
    (For.renameOperands rename operands).eval target = operands.eval source := by
  induction operands with
  | nil => rfl
  | cons _ _ ih => simp only [For.renameOperands, Operands.eval, same, ih]

private theorem evalAppendOperands (head : Operands Γ Δ) (tail : Operands Γ args) (env : Env Γ) :
    (appendOperands tail head).eval env = (head.eval env).append (tail.eval env) := by
  induction head with
  | nil => rfl
  | cons _ _ ih => simp only [appendOperands, Operands.eval, Env.append, ih]

variable {extra : List Width}

private theorem evalEdgeWith (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (kept : Operands Δ (extra ++ [saved])) (edge : Edge (SourceLabel carried result) Γ) :
    (routeEdgeWith rename kept edge).eval target = carryFrameWith (kept.eval target) (edge.eval source) := by
  cases edge with
  | mk label args =>
    cases label
    · change (⟨Label.header, (appendOperands (For.renameOperands rename args) kept).eval target⟩ :
        Frame (Label saved carried result extra)) = ⟨.header, (kept.eval target).append (args.eval source)⟩
      rw [evalAppendOperands, evalRename _ _ _ same]
    · change (⟨Label.exit, (For.renameOperands rename args).eval target⟩ :
        Frame (Label saved carried result extra)) = ⟨.exit, args.eval source⟩
      rw [evalRename _ _ _ same]

private theorem evalTermWith (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (kept : Operands Δ (extra ++ [saved])) (term : Terminator (SourceLabel carried result) [result] Γ) :
    (routeTermWith rename kept term).eval target =
      (term.eval source).map (carryFrameWith (kept.eval target)) id := by
  cases term with
  | br edge => simp [routeTermWith, Terminator.eval, evalEdgeWith _ _ _ same, Sum.map]
  | ret returns => simp [routeTermWith, Terminator.eval, evalRename _ _ _ same, Sum.map]
  | condBr test onTrue onFalse =>
    simp only [routeTermWith, Terminator.eval, same, evalEdgeWith _ _ _ same]
    cases (source.get test).getLsbD 0 <;> rfl

private theorem evalCodeWith (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (kept : Operands Δ (extra ++ [saved])) :
    (routeCodeWith rename kept code).eval evalOp (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map
        (carryFrameWith (kept.eval target)) id := by
  induction code generalizing Δ with
  | terminator term => exact evalTermWith rename source target same kept term
  | letOp op operands rest ih =>
    simp only [routeCodeWith, Code.eval, evalRename _ _ _ same]
    have lifted := evalRename Var.there target (.cons (evalOp op (operands.eval source)) target)
      (fun _ => rfl) kept
    rw [← lifted]
    apply ih
    intro w ref
    cases ref with
    | here => rfl
    | there ref => exact same ref

private theorem evalCode (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (keep : Var Δ saved) :
    (routeCode rename keep code).eval evalOp (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map (carryFrame (target.get keep)) id :=
  evalCodeWith (extra := []) (saved := saved) code rename source target same (.cons keep .nil)

private theorem picked_spec (picked : pickAndHoist? g tree = some (cut, output)) :
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args) (captured : Operands Input args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧
      LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest) = some cut ∧
      cut = ⟨none, 0⟩ ∧ capture? operands = some captured ∧
      output.2 = emit (lower g).entry op captured rest := by
  unfold pickAndHoist? at picked
  cases header : (lower g).block .header with
  | terminator term => simp [header] at picked
  | letOp op operands rest =>
    rw [header] at picked
    obtain ⟨chosen, selected, emitted⟩ := Option.bind_eq_some_iff.mp picked
    split at emitted
    · rename_i hCut
      obtain ⟨captured, capturedEq, paired⟩ := Option.bind_eq_some_iff.mp emitted
      cases paired
      have preheader : cut = ⟨none, 0⟩ := by
        cases cut with
        | mk block pos => cases block <;> simp_all
      exact ⟨_, op, operands, captured, rest, rfl, selected, preheader, capturedEq, rfl⟩
    · contradiction

theorem pickAndHoist?_placement (picked : pickAndHoist? g tree = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧
      LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest) = some cut ∧
      Legal (lower g) (operandSites operands) (useSites 0 1 rest) cut := by
  obtain ⟨_, op, operands, _, rest, header, ranked, preheader, _, _⟩ := picked_spec picked
  obtain ⟨candidate, legal⟩ := LoopForest.choosePlacement_sound ranked
  exact ⟨preheader, candidate, _, op, operands, rest, header, ranked, legal⟩

private theorem evalEntry (op : TargetOp args saved) (captured : Operands Input args)
    (rest : Block TargetOp (SourceLabel carried result) (saved :: carried :: Input) [result])
    (input : Env Input) :
    let value := evalOp op (captured.eval input)
    (emit (lower g).entry op captured rest).entry.eval evalOp (fun term env => Terminator.eval env term)
        input =
      ((lower g).entry.eval evalOp (fun term env => Terminator.eval env term) input).map
        (carryFrame value) id :=
  evalCode (lower g).entry Var.there input (.cons (evalOp op (captured.eval input)) input)
    (fun _ => rfl) .here

private theorem evalBlock (op : TargetOp args saved)
    (operands : Operands (carried :: Input) args) (captured : Operands Input args)
    (rest : Block TargetOp (SourceLabel carried result) (saved :: carried :: Input) [result])
    (header : (lower g).block .header = .letOp op operands rest)
    (capture : capture? operands = some captured) (input : Env Input)
    (frame : Frame (SourceLabel carried result)) :
    let target := emit (lower g).entry op captured rest
    let value := evalOp op (captured.eval input)
    let routed := carryFrame value frame
    (target.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
      (routed.args.append input) =
      (((lower g).block frame.label).eval evalOp (fun term env => Terminator.eval env term)
        (frame.args.append input)).map (carryFrame value) id := by
  cases frame with
  | mk label values =>
    cases label with
    | exit => rfl
    | header =>
      cases values with
      | cons old tail =>
        cases tail
        let value := evalOp op (captured.eval input)
        change (routeCode (fun ref => ref) .here rest).eval evalOp (fun term env => Terminator.eval env term)
            (.cons value (.cons old input)) =
          (((lower g).block .header).eval evalOp (fun term env => Terminator.eval env term)
            (.cons old input)).map (carryFrame value) id
        rw [header, Code.eval, evalCapture operands capture input old]
        exact evalCode rest (fun ref => ref) _ _ (fun _ => rfl) .here

theorem pickAndHoist?_routes (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) :
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args) (captured : Operands Input args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧ capture? operands = some captured ∧
      let value := evalOp op (captured.eval input)
      output.2.entry.eval evalOp (fun term env => Terminator.eval env term) input =
        ((lower g).entry.eval evalOp (fun term env => Terminator.eval env term) input).map
          (carryFrame value) id ∧
      ∀ frame : Frame (SourceLabel carried result),
        let routed := carryFrame value frame
        (output.2.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
          (routed.args.append input) =
          (((lower g).block frame.label).eval evalOp (fun term env => Terminator.eval env term)
            (frame.args.append input)).map (carryFrame value) id := by
  obtain ⟨_, op, operands, captured, rest, header, _, _, capture, emitted⟩ := picked_spec picked
  rw [emitted]
  exact ⟨_, op, operands, captured, rest, header, capture, evalEntry op captured rest input,
    evalBlock op operands captured rest header capture input⟩

private theorem runEqOfRoutes
    {source : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {target : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (routing : RoutesWith source target input values) (fuel : Nat) :
    target.run evalOp fuel input = source.run evalOp fuel input := by
  have runs (fuel : Nat) (frame : Frame (SourceLabel carried result)) :
      target.runFrom evalOp fuel input (carryFrameWith values frame) =
        source.runFrom evalOp fuel input frame := by
    induction fuel generalizing frame with
    | zero => rfl
    | succ fuel ih =>
      unfold Cfg.runFrom
      rw [Cfg.runBlock, Cfg.runBlock, routing.block]
      cases ((source.block frame.label).eval evalOp (fun term env => Terminator.eval env term)
          (frame.args.append input)) with
      | inr returned => rfl
      | inl next => exact ih next
  cases fuel with
  | zero => rfl
  | succ fuel =>
    unfold Cfg.run
    rw [Cfg.runBlock, Cfg.runBlock, routing.entry]
    cases (source.entry.eval evalOp (fun term env => Terminator.eval env term) input) with
    | inr returned => rfl
    | inl next => exact runs fuel next

theorem pickAndHoist?_run_eq (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, op, _, captured, _, _, _, entry, block⟩ := pickAndHoist?_routes picked input
  exact runEqOfRoutes (values := .cons (evalOp op (captured.eval input)) .nil) ⟨entry, block⟩ fuel

theorem pickAndHoist?_budget (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickAndHoist?_run_eq picked input (budget + 3)).trans (lower_run g input budget)

theorem pickAndHoist?_returns_iff (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  (lower_returns_iff g input value).trans
    (exists_congr (fun fuel => by rw [← pickAndHoist?_run_eq picked input fuel]))


private def CapturesAgree (origins : Origins Input Γ) (env : Env Γ) (input : Env Input) : Prop :=
  ∀ {w} (ref : Var Γ w) (captured : Var Input w),
    origins ref = .inl captured → env.get ref = input.get captured

private theorem headerCapturesAgree (old : BitVec carried.val) (input : Env Input) :
    CapturesAgree headerOrigins (.cons old input) input := by
  intro _ ref cap origin
  cases ref with
  | here => cases origin
  | there ref => cases origin; rfl

private theorem evalCaptureOrigins (origins : Origins Input Γ)
    (operands : Operands Γ args) {captured : Operands Input args}
    (found : captureOrigins? origins operands = some captured)
    (env : Env Γ) (input : Env Input) (agree : CapturesAgree origins env input) :
    operands.eval env = captured.eval input := by
  induction operands with
  | nil => cases found; rfl
  | cons head rest ih =>
    cases origin : origins head with
    | inr cut => simp [captureOrigins?, origin] at found
    | inl ref =>
      simp only [captureOrigins?, origin, Option.map_eq_some_iff] at found
      obtain ⟨tail, translated, rfl⟩ := found
      simp only [Operands.eval, agree head ref origin, ih translated]

private theorem evalBinding
    (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (index level : Nat) (origins : Origins Input Γ)
    (binding : Binding Input Γ saved carried result)
    (found : findBinding index level origins code = some ⟨saved, binding⟩)
    (operands : Operands Input binding.args) (captured : binding.captured? = some operands)
    (input : Env Input) (source : Env Γ) (agree : CapturesAgree origins source input)
    (target : Env Δ) (rename : Rename Γ Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (keep : Var Δ saved) (value : target.get keep = evalOp binding.op (operands.eval input)) :
    (binding.rewrite rename keep).eval evalOp (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map
        (carryFrame (target.get keep)) id := by
  induction code generalizing index level Δ with
  | terminator => simp [findBinding] at found
  | letOp op inputs rest ih =>
    cases index with
    | zero =>
      cases found
      have evalOperands := evalCaptureOrigins origins inputs captured source input agree
      rw [Code.eval, evalOperands, ← value]
      apply evalCode
      intro _ ref
      cases ref with
      | here => rfl
      | there ref => exact same ref
    | succ index =>
      simp only [findBinding, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, later⟩, found, paired⟩ := found
      cases paired
      simp only [Binding.prepend, Code.eval, evalRename _ _ _ same]
      apply ih index (level + 1) (afterBinding origins (level + 1)) later found
        operands captured
      · intro _ ref cap origin
        cases ref with
        | here => cases origin
        | there ref => exact agree ref cap origin
      · intro _ ref
        cases ref with
        | here => rfl
        | there ref => exact same ref
      · exact value


variable {index : Nat}

private theorem nominated_spec (picked : pickBindingAndHoist? g tree index = some (cut, output)) :
    ∃ binding : Binding Input (carried :: Input) output.1 carried result,
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      LoopForest.choosePlacement tree blocks binding.operands binding.uses = some cut ∧
      cut = ⟨none, 0⟩ ∧
      ∃ operands : Operands Input binding.args,
        binding.captured? = some operands ∧
        output.2 = emitHeader (lower g).entry binding.op operands (binding.rewrite Var.there .here) := by
  unfold pickBindingAndHoist? hoistBindingWith? at picked
  obtain ⟨⟨_, binding⟩, found, ranked⟩ := Option.bind_eq_some_iff.mp picked
  obtain ⟨chosen, selected, emitted⟩ := Option.bind_eq_some_iff.mp ranked
  split at emitted
  · rename_i atEntry
    obtain ⟨operands, captured, paired⟩ := Option.bind_eq_some_iff.mp emitted
    cases paired
    have preheader : cut = ⟨none, 0⟩ := by
      cases cut with
      | mk block pos => cases block <;> simp_all
    exact ⟨binding, found, selected, preheader, operands, captured, rfl⟩
  · contradiction

theorem pickBindingAndHoist?_placement (picked : pickBindingAndHoist? g tree index = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
    ∃ binding : Binding Input (carried :: Input) output.1 carried result,
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      LoopForest.choosePlacement tree blocks binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut := by
  obtain ⟨binding, found, ranked, preheader, _⟩ := nominated_spec picked
  obtain ⟨candidate, legal⟩ := LoopForest.choosePlacement_sound ranked
  exact ⟨preheader, candidate, binding, found, ranked, legal⟩

theorem pickBindingAndHoist?_routes (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) :
    ∃ (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes (lower g) output.2 input (evalOp binding.op (operands.eval input)) := by
  obtain ⟨binding, found, _, _, operands, captured, emitted⟩ := nominated_spec picked
  rw [emitted]
  refine ⟨binding, operands, found, captured, ⟨?_, ?_⟩⟩
  · exact evalCode (lower g).entry Var.there input (.cons (evalOp binding.op (operands.eval input)) input)
      (fun _ => rfl) .here
  · intro frame
    cases frame with
    | mk label values =>
      cases label with
      | exit => rfl
      | header =>
        cases values with
        | cons old tail =>
          cases tail
          exact evalBinding ((lower g).block .header) index 0 headerOrigins binding found
            operands captured input (.cons old input) (headerCapturesAgree old input)
            (.cons (evalOp binding.op (operands.eval input)) (.cons old input))
            Var.there (fun _ => rfl) .here rfl

theorem pickBindingAndHoist?_run_eq (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨binding, operands, _, _, routing⟩ := pickBindingAndHoist?_routes picked input
  exact runEqOfRoutes (values := .cons (evalOp binding.op (operands.eval input)) .nil)
    ⟨routing.entry, routing.block⟩ fuel

theorem pickBindingAndHoist?_budget (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickBindingAndHoist?_run_eq picked input (budget + 3)).trans (lower_run g input budget)

theorem pickBindingAndHoist?_returns_iff
    (picked : pickBindingAndHoist? g tree index = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  (lower_returns_iff g input value).trans
    (exists_congr (fun fuel => by rw [← pickBindingAndHoist?_run_eq picked input fuel]))


private theorem afterPrerequisiteAgree {origins : Origins Input Γ} {source : Env Γ}
    {input : Env Input} (agree : CapturesAgree origins source input) (value : BitVec saved.val) :
    CapturesAgree (afterPrerequisite origins) (.cons value source) (.cons value input) := by
  intro w ref captured origin
  cases ref with
  | here => cases origin; rfl
  | there ref =>
    cases previous : origins ref with
    | inr cut => simp [afterPrerequisite, previous, Sum.map] at origin
    | inl inputRef =>
      simp only [afterPrerequisite, previous, Sum.map] at origin
      cases origin
      exact agree ref inputRef previous

variable {prerequisite consumer : Width}

private theorem evalSliceConsumer
    (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (gap level : Nat) (prerequisiteRef : Var Γ prerequisite)
    (origins : Origins (prerequisite :: Input) Γ)
    (binding : SliceConsumer Input Γ prerequisite consumer carried result)
    (found : findSliceConsumer gap level prerequisiteRef origins code = some ⟨consumer, binding⟩)
    (inputs : Env (prerequisite :: Input)) (source : Env Γ) (agree : CapturesAgree origins source inputs)
    (target : Env Δ) (rename : Rename Γ Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (keepConsumer : Var Δ consumer) (keepPrerequisite : Var Δ prerequisite)
    (second : target.get keepConsumer = evalOp binding.op (binding.inputs.eval inputs)) :
    (binding.rewrite rename keepConsumer keepPrerequisite).eval evalOp
        (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map
        (carryFrameWith (extra := [consumer]) (.cons (target.get keepConsumer)
          (.cons (target.get keepPrerequisite) .nil))) id := by
  induction code generalizing gap level Δ with
  | terminator => simp [findSliceConsumer] at found
  | letOp op operands rest ih =>
    cases gap with
    | zero =>
      simp only [findSliceConsumer] at found
      split at found
      · contradiction
      · obtain ⟨captured, capture, paired⟩ := Option.bind_eq_some_iff.mp found
        cases paired
        rw [Code.eval, evalCaptureOrigins origins operands capture source inputs agree, ← second]
        apply evalCodeWith
        intro _ ref
        cases ref with
        | here => rfl
        | there ref => exact same ref
    | succ gap =>
      simp only [findSliceConsumer, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, later⟩, found, paired⟩ := found
      cases paired
      simp only [SliceConsumer.prepend, Code.eval, evalRename _ _ _ same]
      apply ih gap (level + 1) (.there prerequisiteRef) (afterBinding origins (level + 1)) later found
      · intro _ ref cap origin
        cases ref with
        | here => cases origin
        | there ref => exact agree ref cap origin
      · intro _ ref
        cases ref with
        | here => rfl
        | there ref => exact same ref
      · exact second

private theorem evalSlice
    (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (index gap level : Nat) (origins : Origins Input Γ)
    (slice : Slice Input Γ prerequisite consumer carried result)
    (found : findSliceAcross index gap level origins code = some ⟨prerequisite, consumer, slice⟩)
    (input : Env Input) (source : Env Γ) (agree : CapturesAgree origins source input)
    (target : Env Δ) (rename : Rename Γ Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (keepConsumer : Var Δ consumer) (keepPrerequisite : Var Δ prerequisite)
    (first : target.get keepPrerequisite = evalOp slice.prerequisiteOp (slice.prerequisiteInputs.eval input))
    (second : target.get keepConsumer =
      evalOp slice.consumerOp (slice.consumerInputs.eval (.cons (target.get keepPrerequisite) input))) :
    (slice.rewrite rename keepConsumer keepPrerequisite).eval evalOp
        (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map
        (carryFrameWith (extra := [consumer]) (.cons (target.get keepConsumer)
          (.cons (target.get keepPrerequisite) .nil))) id := by
  induction code generalizing index level Δ with
  | terminator => simp [findSliceAcross] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      simp only [findSliceAcross] at found
      obtain ⟨captured, capture, next⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨⟨_, binding⟩, consumerFound, paired⟩ := Option.bind_eq_some_iff.mp next
      cases paired
      rw [Code.eval, evalCaptureOrigins origins operands capture source input agree, ← first]
      refine evalSliceConsumer rest gap (level + 1) .here (afterPrerequisite origins) binding consumerFound
        _ _ (afterPrerequisiteAgree agree (target.get keepPrerequisite)) target
        (replaceBinding rename keepPrerequisite) ?_ keepConsumer keepPrerequisite second
      intro _ ref
      cases ref with
      | here => rfl
      | there ref => exact same ref
    | succ index =>
      simp only [findSliceAcross, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, _, later⟩, found, paired⟩ := found
      cases paired
      simp only [Slice.prepend, Code.eval, evalRename _ _ _ same]
      apply ih index (level + 1) (afterBinding origins (level + 1)) later found
      · intro _ ref cap origin
        cases ref with
        | here => cases origin
        | there ref => exact agree ref cap origin
      · intro _ ref
        cases ref with
        | here => rfl
        | there ref => exact same ref
      · exact first
      · exact second

variable {prerequisiteIndex gap : Nat} {moved : SliceOutput Input carried result}

private theorem atPreheader {site : Point (SourceLabel carried result)}
    (entry : site.block.isNone = true) (zero : (site.cut == 0) = true) :
    site = ⟨none, 0⟩ := by
  cases site with
  | mk block cut => cases block <;> simp_all

private theorem pickedSliceAcross_spec
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved) :
    ∃ slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result,
      findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      LoopForest.choosePlacement tree blocks slice.prerequisiteSites slice.prerequisiteUses = some ⟨none, 0⟩ ∧
      LoopForest.choosePlacement tree blocks slice.consumerSites slice.consumerUses = some ⟨none, 0⟩ ∧
      moved.cfg = (emitSlice (lower g).entry slice).cfg := by
  unfold pickSliceAcrossAndHoist? at picked
  obtain ⟨⟨_, _, slice⟩, found, ranked⟩ := Option.bind_eq_some_iff.mp picked
  obtain ⟨firstCut, firstRank, ranked⟩ := Option.bind_eq_some_iff.mp ranked
  obtain ⟨secondCut, secondRank, emitted⟩ := Option.bind_eq_some_iff.mp ranked
  split at emitted
  · rename_i accepted
    simp only [Bool.and_eq_true] at accepted
    obtain ⟨⟨⟨firstEntry, firstZero⟩, secondEntry⟩, secondZero⟩ := accepted
    cases emitted
    exact ⟨slice, found, firstRank.trans (congrArg some (atPreheader firstEntry firstZero)),
      secondRank.trans (congrArg some (atPreheader secondEntry secondZero)), rfl⟩
  · contradiction

theorem pickSliceAcrossAndHoist?_placement
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved) :
    ∃ slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result,
      findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      (⟨none, 0⟩ : Point (SourceLabel carried result)) ∈ candidateCuts (lower g) blocks ∧
      Legal (lower g) slice.prerequisiteSites slice.prerequisiteUses ⟨none, 0⟩ ∧
      Legal (lower g) slice.consumerSites slice.consumerUses ⟨none, 0⟩ := by
  obtain ⟨slice, found, firstRank, secondRank, _⟩ := pickedSliceAcross_spec picked
  obtain ⟨represented, firstLegal⟩ := LoopForest.choosePlacement_sound firstRank
  exact ⟨slice, found, represented, firstLegal, (LoopForest.choosePlacement_sound secondRank).2⟩

theorem pickSliceAcrossAndHoist?_routes
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved) (input : Env Input) :
    ∃ slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result,
      findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      RoutesWith (lower g) moved.cfg input (slice.savedValues input) := by
  obtain ⟨slice, found, _, _, emitted⟩ := pickedSliceAcross_spec picked
  rw [emitted]
  let first := evalOp slice.prerequisiteOp (slice.prerequisiteInputs.eval input)
  let second := evalOp slice.consumerOp (slice.consumerInputs.eval (.cons first input))
  refine ⟨slice, found, ⟨?_, ?_⟩⟩
  · exact evalCodeWith (extra := [moved.consumer]) (saved := moved.prerequisite) (lower g).entry
      (fun ref => .there (.there ref)) input (.cons second (.cons first input))
      (fun _ => rfl) (.cons .here (.cons (.there .here) .nil))
  · intro frame
    cases frame with
    | mk label values =>
      cases label with
      | exit => rfl
      | header =>
        cases values with
        | cons old tail =>
          cases tail
          exact evalSlice ((lower g).block .header) prerequisiteIndex gap 0 headerOrigins slice found input
            (.cons old input) (headerCapturesAgree old input) (.cons second (.cons first (.cons old input)))
            (fun ref => .there (.there ref)) (fun _ => rfl) .here (.there .here) rfl rfl

theorem pickSliceAcrossAndHoist?_run_eq
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, routing⟩ := pickSliceAcrossAndHoist?_routes picked input
  exact runEqOfRoutes routing fuel

theorem pickSliceAcrossAndHoist?_budget
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickSliceAcrossAndHoist?_run_eq picked input (budget + 3)).trans (lower_run g input budget)

theorem pickSliceAcrossAndHoist?_returns_iff
    (picked : pickSliceAcrossAndHoist? g tree prerequisiteIndex gap = some moved)
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, moved.cfg.run evalOp fuel input = some (.cons value .nil) :=
  (lower_returns_iff g input value).trans
    (exists_congr (fun fuel => by rw [← pickSliceAcrossAndHoist?_run_eq picked input fuel]))

variable {consumerIndex : Nat}

theorem pickSliceAndHoist?_placement (picked : pickSliceAndHoist? g tree consumerIndex = some moved) :
    ∃ (index : Nat)
      (slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result),
      consumerIndex = index + 1 ∧
      findSlice index 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      (⟨none, 0⟩ : Point (SourceLabel carried result)) ∈ candidateCuts (lower g) blocks ∧
      Legal (lower g) slice.prerequisiteSites slice.prerequisiteUses ⟨none, 0⟩ ∧
      Legal (lower g) slice.consumerSites slice.consumerUses ⟨none, 0⟩ := by
  cases consumerIndex with
  | zero => cases picked
  | succ index =>
    obtain ⟨slice, found, represented, firstLegal, secondLegal⟩ :=
      pickSliceAcrossAndHoist?_placement (prerequisiteIndex := index) (gap := 0) picked
    exact ⟨index, slice, rfl, found, represented, firstLegal, secondLegal⟩

theorem pickSliceAndHoist?_routes (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) :
    ∃ (index : Nat)
      (slice : Slice Input (carried :: Input) moved.prerequisite moved.consumer carried result),
      consumerIndex = index + 1 ∧
      findSlice index 0 headerOrigins ((lower g).block .header) = some ⟨_, _, slice⟩ ∧
      RoutesWith (lower g) moved.cfg input (slice.savedValues input) := by
  cases consumerIndex with
  | zero => cases picked
  | succ index =>
    obtain ⟨slice, found, routing⟩ :=
      pickSliceAcrossAndHoist?_routes (prerequisiteIndex := index) (gap := 0) picked input
    exact ⟨index, slice, rfl, found, routing⟩

theorem pickSliceAndHoist?_run_eq (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, _, _, routing⟩ := pickSliceAndHoist?_routes picked input
  exact runEqOfRoutes routing fuel

theorem pickSliceAndHoist?_budget (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickSliceAndHoist?_run_eq picked input (budget + 3)).trans (lower_run g input budget)

theorem pickSliceAndHoist?_returns_iff (picked : pickSliceAndHoist? g tree consumerIndex = some moved)
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, moved.cfg.run evalOp fuel input = some (.cons value .nil) :=
  (lower_returns_iff g input value).trans
    (exists_congr (fun fuel => by rw [← pickSliceAndHoist?_run_eq picked input fuel]))


end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist
