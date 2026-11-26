module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.CopyChain
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Soundness
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison

variable {V F α : Type} [DecidableEq V] {a b : Nat}
variable {graph : Graph V F a b}

private def Visited (remaining : Finset (Fin graph.locals)) : Label graph.locals b → Prop
  | .inl index => index ∉ remaining
  | .inr _ => False

/-- Every visited block lies on a nonempty typed walk to the current
label. Its first edge stays among visited blocks or reaches the current
label directly. A repeat closes the visited set. -/
private def LinksBack (remaining : Finset (Fin graph.locals)) (current : Label graph.locals b) : Prop :=
  ∀ i, i ∉ remaining → ∃ next, next? graph i = some next ∧
    (next = current ∨ Visited (graph := graph) remaining next) ∧ Reaches graph next current

private def Closed (remaining : Finset (Fin graph.locals)) : Prop :=
  ∀ i, i ∉ remaining → ∃ next, next? graph i = some next ∧ Visited (graph := graph) remaining next

private def TypedFrom (start : Label graph.locals b) : Prop :=
  ∀ i, Reaches graph start (.inl i) → ∃ next, PacketCopy.Forwards {(graph.block i).param} (graph.block i).body next

private def Spec (start : Label graph.locals b) : Outcome graph.locals b → Prop
  | .returns port => ∃ trace, Path graph start trace port
  | .cycle i => Reaches graph start (.inl i) ∧ LoopsAt graph i ∧
      (∃ remaining, i ∉ remaining ∧ Closed (graph := graph) remaining) ∧ TypedFrom (graph := graph) start
  | .unsupported i => Reaches graph start (.inl i) ∧ next? graph i = none

private theorem reaches_trans {start middle finish : Label graph.locals b}
    (first : Reaches graph start middle) (second : Reaches graph middle finish) :
    Reaches graph start finish := by
  induction first with
  | here => exact second
  | step edge _ ih => exact .step edge (ih second)

private theorem advance {remaining : Finset (Fin graph.locals)} {index : Fin graph.locals}
    {next : Label graph.locals b} (links : LinksBack remaining (.inl index))
    (edge : next? graph index = some next) :
    LinksBack (remaining.erase index) next := by
  intro i absent
  by_cases same : i = index
  · subst i
    exact ⟨next, edge, Or.inl rfl, .here next⟩
  · have old : i ∉ remaining := fun member => absent (Finset.mem_erase.mpr ⟨same, member⟩)
    obtain ⟨target, checked, location, walk⟩ := links i old
    refine ⟨target, checked, Or.inr ?_, reaches_trans walk (.step (next_iff.mp edge) (.here next))⟩
    rcases location with rfl | visited
    · exact fun member => (Finset.mem_erase.mp member).1 rfl
    · cases target with
      | inl label => exact fun member => visited (Finset.mem_erase.mp member).2
      | inr port => exact visited

private theorem same_target {i : Fin graph.locals} {target other : Label graph.locals b}
    (edge : PacketCopy.Forwards {(graph.block i).param} (graph.block i).body target)
    (checked : next? graph i = some other) : target = other :=
  Option.some.inj ((next_iff.mpr edge).symm.trans checked)

private theorem typed_step {i : Fin graph.locals} {next : Label graph.locals b}
    (edge : PacketCopy.Forwards {(graph.block i).param} (graph.block i).body next)
    (tail : TypedFrom (graph := graph) next) : TypedFrom (graph := graph) (.inl i) := by
  intro index reached
  cases reached with
  | here => exact ⟨next, edge⟩
  | step other rest =>
    cases same_target other (next_iff.mpr edge)
    exact tail index rest

private theorem typed_path {start : Label graph.locals b} {trace : List (Fin graph.locals)} {port : Fin b}
    (path : Path graph start trace port) : TypedFrom (graph := graph) start := by
  induction path with
  | exit port => intro i reached; cases reached
  | step edge _ ih => exact typed_step edge ih

private theorem closed_reaches {remaining : Finset (Fin graph.locals)}
    {start finish : Label graph.locals b} (closed : Closed (graph := graph) remaining)
    (walk : Reaches graph start finish) (visited : Visited (graph := graph) remaining start) :
    Visited (graph := graph) remaining finish := by
  induction walk with
  | here label => exact visited
  | @step i next finish edge tail ih =>
    obtain ⟨target, checked, targetVisited⟩ := closed i visited
    cases same_target edge checked
    exact ih targetVisited

private theorem typed_closed {remaining : Finset (Fin graph.locals)} {i : Fin graph.locals}
    (closed : Closed (graph := graph) remaining) (visited : i ∉ remaining) :
    TypedFrom (graph := graph) (.inl i) := by
  intro index walk
  obtain ⟨next, checked, _⟩ := closed index (closed_reaches closed walk visited)
  exact ⟨next, next_iff.mp checked⟩

private theorem inspect_spec (remaining : Finset (Fin graph.locals)) (start : Label graph.locals b)
    (links : LinksBack remaining start) : Spec start (inspect graph remaining start) := by
  induction remaining using Finset.strongInductionOn generalizing start with
  | _ remaining ih =>
    rw [inspect.eq_def]
    cases start with
    | inr port => exact ⟨[], .exit port⟩
    | inl i =>
      by_cases fresh : i ∈ remaining
      · simp only [dite_eq_left fresh]
        cases edge : next? graph i with
        | none => exact ⟨.here _, edge⟩
        | some next =>
          change Spec (.inl i) (inspect graph (remaining.erase i) next)
          have typed := next_iff.mp edge
          have tail := ih (remaining.erase i) (Finset.erase_ssubset fresh) next (advance links edge)
          cases result : inspect graph (remaining.erase i) next with
          | returns port =>
            rw [result] at tail
            obtain ⟨trace, path⟩ := tail
            exact ⟨i :: trace, .step typed path⟩
          | cycle repeated =>
            rw [result] at tail
            obtain ⟨reached, loop, closed, supported⟩ := tail
            exact ⟨.step typed reached, loop, closed, typed_step typed supported⟩
          | unsupported index =>
            rw [result] at tail
            exact ⟨.step typed tail.1, tail.2⟩
      · simp only [dite_eq_right fresh]
        have closed : Closed (graph := graph) remaining := by
          intro index visited
          obtain ⟨next, checked, rfl | known, _⟩ := links index visited
          · exact ⟨.inl i, checked, fresh⟩
          · exact ⟨next, checked, known⟩
        obtain ⟨next, checked, _, loop⟩ := links i fresh
        exact ⟨.here _, ⟨next, next_iff.mp checked, loop⟩, ⟨remaining, fresh, closed⟩, typed_closed closed fresh⟩

private theorem entry_spec (input : Fin a) :
    Spec (graph.entry input) (entryOutcome graph input) :=
  inspect_spec _ _ (fun _ absent => (absent (Finset.mem_univ _)).elim)

theorem entry_returns (model : Model F Part α) (input : Fin a × α) (port : Fin b)
    (found : entryOutcome graph input.1 = .returns port) :
    graph.denote model input = pure (port, input.2) := by
  have spec := entry_spec (graph := graph) input.1
  rw [found] at spec
  exact denote_of_terminal model input port (terminal_iff.mpr spec)

theorem entry_unsupported (input : Fin a) (i : Fin graph.locals)
    (found : entryOutcome graph input = .unsupported i) :
    Reaches graph (graph.entry input) (.inl i) ∧
      ¬ ∃ next, PacketCopy.Forwards {(graph.block i).param} (graph.block i).body next := by
  have spec := entry_spec (graph := graph) input
  rw [found] at spec
  refine ⟨spec.1, ?_⟩
  rintro ⟨next, typed⟩
  have edge := next_iff.mpr typed
  rw [spec.2] at edge
  contradiction

private theorem no_closed_run (model : Model F Part α) {remaining : Finset (Fin graph.locals)}
    (closed : Closed (graph := graph) remaining) {start : Label graph.locals b × α} {result : Fin b × α}
    (run : Silmaril.Elgot.Part.Runs (graph.step model) start result)
    (visited : Visited (graph := graph) remaining start.1) : False := by
  induction run with
  | @done start result returned =>
    rcases start with ⟨index | port, packet⟩
    · simp [Graph.step, Part.mem_map_iff] at returned
    · exact visited
  | @more start next result advanced _ ih =>
    rcases start with ⟨index | port, packet⟩
    · obtain ⟨target, checked, known⟩ := closed index visited
      rw [Simulation.forwardingStep model index target packet (next_iff.mp checked)] at advanced
      have equal : next = (target, packet) := by simpa using advanced
      exact ih (equal ▸ known)
    · exact visited

private theorem iter_reaches (model : Model F Part α) (packet : α) {start finish : Label graph.locals b}
    (walk : Reaches graph start finish) :
    iter (graph.step model) (start, packet) = iter (graph.step model) (finish, packet) := by
  induction walk with
  | here label => rfl
  | @step index next finish edge tail ih =>
    rw [congrFun (LawfulElgotMonad.fixpoint _) _, Simulation.forwardingStep model index next packet edge]
    rw [← Part.pure_eq_some, pure_bind]
    exact ih

theorem entry_cycle (model : Model F Part α) (input : Fin a × α) (i : Fin graph.locals)
    (found : entryOutcome graph input.1 = .cycle i) :
    (Reaches graph (graph.entry input.1) (.inl i) ∧ LoopsAt graph i) ∧
      graph.denote model input = Part.none := by
  have spec := entry_spec (graph := graph) input.1
  rw [found] at spec
  obtain ⟨walk, loop, ⟨remaining, visited, closed⟩, _⟩ := spec
  refine ⟨⟨walk, loop⟩, ?_⟩
  unfold Graph.denote
  rw [iter_reaches model input.2 walk]
  apply Part.eq_none_iff.mpr
  intro result member
  exact no_closed_run model closed ((Silmaril.Elgot.Part.mem_iter_iff _ _ result).mp member) visited

private def Supported {n : Nat} : Outcome n b → Prop
  | .unsupported _ => False
  | _ => True

private theorem all_supported : EntryTyped graph ↔ ∀ input, Supported (entryOutcome graph input) := by
  constructor
  · intro typed input
    cases found : entryOutcome graph input with
    | returns port => trivial
    | cycle i => trivial
    | unsupported i =>
      have failure := entry_unsupported input i found
      exact failure.2 (typed input i failure.1)
  · intro supported input
    have spec := entry_spec (graph := graph) input
    cases found : entryOutcome graph input with
    | returns port =>
      rw [found] at spec
      obtain ⟨trace, path⟩ := spec
      exact typed_path path
    | cycle i =>
      rw [found] at spec
      obtain ⟨_, _, _, typed⟩ := spec
      exact typed
    | unsupported i =>
      have supportedInput := supported input
      rw [found] at supportedInput
      exact supportedInput.elim

private theorem compare_supported {n m : Nat} (left : Outcome n b) (right : Outcome m b) :
    (left.refines? right).isSome ↔ Supported left ∧ Supported right := by
  cases left <;> cases right <;> simp [Outcome.refines?, Outcome.agrees?, Supported]

private theorem entry_agrees (model : PairModel F Part α) (left right : Graph V F a b) (input : Fin a)
    (leftOK : Supported (entryOutcome left input)) (rightOK : Supported (entryOutcome right input)) :
    (entryOutcome left input).refines? (entryOutcome right input) = some true ↔
      ∀ (m : PairModel F Part α) (packet : α), left.denote m.val (input, packet) ≤ right.denote m.val (input, packet) := by
  cases source : entryOutcome left input with
  | unsupported i =>
    rw [source] at leftOK
    exact leftOK.elim
  | cycle i =>
    have included (m : PairModel F Part α) (packet : α) :
        left.denote m.val (input, packet) ≤ right.denote m.val (input, packet) := by
      rw [(entry_cycle m.val (input, packet) i source).2]
      exact fun result member => (Part.notMem_none result member).elim
    cases target : entryOutcome right input with
    | unsupported j =>
      rw [target] at rightOK
      exact rightOK.elim
    | returns port => exact ⟨fun _ => included, fun _ => rfl⟩
    | cycle j => exact ⟨fun _ => included, fun _ => rfl⟩
  | returns sourcePort =>
    cases target : entryOutcome right input with
    | unsupported j =>
      rw [target] at rightOK
      exact rightOK.elim
    | cycle j =>
      simp only [Outcome.refines?, Option.some.injEq, Bool.false_eq_true, false_iff]
      intro included
      have atUnit := included model model.val.unit
      rw [entry_returns model.val (input, model.val.unit) sourcePort source,
        (entry_cycle model.val (input, model.val.unit) j target).2] at atUnit
      exact Part.notMem_none _ (atUnit _ (Part.mem_some _))
    | returns targetPort =>
      simp only [Outcome.refines?, Outcome.agrees?, Option.some.injEq, decide_eq_true_eq]
      constructor
      · intro same m packet
        rw [entry_returns m.val (input, packet) sourcePort source,
          entry_returns m.val (input, packet) targetPort target, same]
      · intro included
        have atUnit := included model model.val.unit
        rw [entry_returns model.val (input, model.val.unit) sourcePort source,
          entry_returns model.val (input, model.val.unit) targetPort target] at atUnit
        have same := Part.mem_some_iff.mp (atUnit _ (Part.mem_some _))
        exact congrArg Prod.fst same

private theorem all_agree (model : PairModel F Part α) (left right : Graph V F a b)
    (leftTyped : EntryTyped left) (rightTyped : EntryTyped right) :
    (∀ input, (entryOutcome left input).refines? (entryOutcome right input) = some true) ↔
      Refines (Quotient.mk _ left : Arrow V F α a b) (Quotient.mk _ right) := by
  have each := fun input =>
    entry_agrees model left right input (all_supported.mp leftTyped input) (all_supported.mp rightTyped input)
  exact ⟨fun agrees m input => (each input.1).mp (agrees input.1) m input.2,
    fun included input => (each input).mpr (fun m packet => included m (input, packet))⟩

private theorem supported_eq (left right : Graph V F a b) :
    ((List.finRange a).map (fun input => (entryOutcome left input).refines? (entryOutcome right input))).all
      Option.isSome = true ↔ EntryTyped left ∧ EntryTyped right := by
  simp only [List.all_eq_true, List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, compare_supported, all_supported, forall_and]

theorem refinement_between_none (left right : Graph V F a b) :
    refinementBetween? left right = none ↔ ¬ (EntryTyped left ∧ EntryTyped right) := by
  dsimp only [refinementBetween?]
  split
  · rename_i supported
    simp [(supported_eq left right).mp supported]
  · rename_i unsupported
    simp [mt (supported_eq left right).mpr unsupported]

theorem refinement_between_some (model : PairModel F Part α) (left right : Graph V F a b)
    (verdict : Bool) :
    refinementBetween? left right = some verdict ↔ (EntryTyped left ∧ EntryTyped right) ∧
      (verdict = true ↔ Refines (Quotient.mk _ left : Arrow V F α a b) (Quotient.mk _ right)) := by
  dsimp only [refinementBetween?]
  split
  · rename_i supported
    have typed := (supported_eq left right).mp supported
    simp only [Option.some.injEq, typed, true_and]
    rw [← all_agree model left right typed.1 typed.2]
    cases verdict <;> simp [List.all_eq_true]
  · rename_i unsupported
    simp [mt (supported_eq left right).mpr unsupported]

private theorem entry_wiring (wire : Fin a → Fin b) (input : Fin a) :
    entryOutcome (Graph.wiring (V := V) (F := F) wire) input = .returns (wire input) := by
  unfold entryOutcome
  rw [inspect.eq_def]
  rfl

theorem refinement_between_wiring (graph : Graph V F a b) (wire : Fin a → Fin b) :
    refinementBetween? graph (Graph.wiring wire) = refinement? graph wire := by
  simp only [refinementBetween?, refinement?, entry_wiring, Outcome.refines?]

private theorem typed_wiring (wire : Fin a → Fin b) : EntryTyped (Graph.wiring (V := V) (F := F) wire) :=
  fun _ index _ => Fin.elim0 index

theorem refinement_none (graph : Graph V F a b) (wire : Fin a → Fin b) :
    refinement? graph wire = none ↔ ¬ EntryTyped graph := by
  rw [← refinement_between_wiring, refinement_between_none]
  simp [typed_wiring]

theorem refinement_some (model : PairModel F Part α) (graph : Graph V F a b)
    (wire : Fin a → Fin b) (verdict : Bool) :
    refinement? graph wire = some verdict ↔ EntryTyped graph ∧
      (verdict = true ↔ Refines (Quotient.mk _ graph : Arrow V F α a b) (Quotient.mk _ (Graph.wiring wire))) := by
  rw [← refinement_between_wiring, refinement_between_some model]
  simp only [typed_wiring, and_true]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain
