module

public import Silmaril.Formats.Bao.Defs

public section

namespace Silmaril.Proofs.Formats.Bao

open Silmaril.Formats.Bao

theorem enqueue_rooted {hash : HashOps} {tree node : Plan} {digest expected : Digest}
    {root : Bool} {tail : List Work} (path : AuthPath hash tree digest node expected root)
    (known : ∀ work ∈ tail, AuthPath hash tree digest work.node work.expected work.root) :
    ∀ work ∈ enqueue node expected root tail,
      AuthPath hash tree digest work.node work.expected work.root := by
  cases node <;> simp only [enqueue, List.mem_cons, forall_eq_or_imp] <;>
    first | exact known | exact ⟨path, known⟩

theorem start_rooted (hash : HashOps) (tree : Plan) (digest : Digest) :
    Rooted hash tree digest (start tree digest) :=
  enqueue_rooted .root (by simp)

theorem step_checked {hash : HashOps} {tree : Plan} {digest : Digest} {size : Nat}
    {state next : Session} {bytes : Bytes} {event : Event}
    (known : Rooted hash tree digest state)
    (accepted : step hash size state bytes = some (next, event)) :
    Rooted hash tree digest next ∧ Checked hash tree digest event ∧
      (next.rightEdge = true ↔ state.rightEdge = true ∨ EdgeEvent size event) := by
  cases state with
  | mk pending edge =>
    cases pending with
    | nil => simp [step] at accepted
    | cons work tail =>
      obtain ⟨node, expected, root⟩ := work
      have atHead := known ⟨node, expected, root⟩ (by simp)
      have atTail : ∀ work ∈ tail, AuthPath hash tree digest work.node work.expected work.root :=
        fun work mem => known work (List.mem_cons_of_mem _ mem)
      cases node with
      | skip => simp [step] at accepted
      | leaf span width =>
        simp only [step] at accepted
        split at accepted
        · next checks =>
          have ⟨lengthEq, digestEq⟩ : bytes.length = width ∧
              hash.subtree root span.first bytes = expected := by simpa using checks
          cases accepted
          subst width
          subst expected
          exact ⟨atTail, .data atHead, by simp [EdgeEvent]⟩
        · contradiction
      | fork span left right =>
        cases pair : splitPair bytes with
        | none => simp [step, pair] at accepted
        | some digests =>
          obtain ⟨leftCV, rightCV⟩ := digests
          by_cases digestEq : hash.parent root leftCV rightCV = expected
          · simp [step, pair, digestEq] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            subst expected
            exact ⟨enqueue_rooted (.left atHead) (enqueue_rooted (.right atHead) atTail),
              .parent atHead, by simp [EdgeEvent]⟩
          · simp [step, pair, digestEq] at accepted

theorem steps_checked {hash : HashOps} {size : Nat} {state final : Session}
    {fields : List Bytes} {events : List Event} (trace : Steps hash size state fields events final)
    {tree : Plan} {digest : Digest} (known : Rooted hash tree digest state) :
    Rooted hash tree digest final ∧ (∀ event ∈ events, Checked hash tree digest event) ∧
      (final.rightEdge = true ↔ state.rightEdge = true ∨ ∃ event ∈ events, EdgeEvent size event) := by
  induction trace with
  | nil => simp [known]
  | cons accepted _ ih =>
    obtain ⟨nextRooted, checked, nextEdge⟩ := step_checked known accepted
    obtain ⟨finalRooted, allChecked, edge⟩ := ih nextRooted
    refine ⟨finalRooted, ?_, ?_⟩
    · intro event mem
      rcases List.mem_cons.mp mem with rfl | found
      · exact checked
      · exact allChecked event found
    · simp only [edge, nextEdge, List.mem_cons, exists_eq_or_imp, or_assoc]

theorem release_checked {hash : HashOps} {size : Nat} {tree : Plan} {digest : Digest}
    {fields : List Bytes} {events : List Event} {final : Session}
    (trace : Steps hash size (start tree digest) fields events final) :
    (∀ event ∈ events, Checked hash tree digest event) ∧
      (rightEdgeClaim size final = some size ↔ ∃ event ∈ events, EdgeEvent size event) := by
  obtain ⟨_, checked, edge⟩ := steps_checked trace (start_rooted hash tree digest)
  exact ⟨checked, by simpa [rightEdgeClaim, start] using edge⟩

theorem runSteps_spec {hash : HashOps} {size : Nat} {state final : Session}
    {fields : List Bytes} {events : List Event} :
    runSteps hash size state fields = some (events, final) ↔ Steps hash size state fields events final := by
  constructor
  · induction fields generalizing state events with
    | nil => intro parsed; cases parsed; exact .nil
    | cons bytes fields ih =>
      intro parsed
      cases accepted : step hash size state bytes with
      | none => simp [runSteps, accepted] at parsed
      | some value =>
        obtain ⟨next, event⟩ := value
        cases remaining : runSteps hash size next fields with
        | none => simp [runSteps, accepted, remaining] at parsed
        | some value =>
          obtain ⟨eventsFound, finalFound⟩ := value
          simp [runSteps, accepted, remaining] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          exact .cons accepted (ih remaining)
  · intro trace
    induction trace with
    | nil => rfl
    | cons accepted _ ih => simp [runSteps, accepted, ih]

theorem verifyFrame_sound {hash : HashOps} {size : Nat} {tree : Plan} {digest : Digest}
    {body : Bytes} {events : List Event} {length : Option Nat}
    (verified : verifyFrame hash size tree digest body = some (events, length)) :
    (∀ event ∈ events, Checked hash tree digest event) ∧
      (length = some size ↔ ∃ event ∈ events, EdgeEvent size event) := by
  cases framed : readFrame tree.preorder body with
  | none => simp [verifyFrame, framed] at verified
  | some fields =>
    cases verifiedSteps : runSteps hash size (start tree digest) fields with
    | none => simp [verifyFrame, framed, verifiedSteps] at verified
    | some result =>
      obtain ⟨observed, state⟩ := result
      cases ended : finished state [] true <;> simp [verifyFrame, framed, verifiedSteps, ended] at verified
      obtain ⟨rfl, rfl⟩ := verified
      exact release_checked (runSteps_spec.mp verifiedSteps)

end Silmaril.Proofs.Formats.Bao
