module

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Tests

open OrderedRuntime.Structured

private abbrev dataPorts : Ports (Ty Unit) := [.value ()]
private abbrev bodyPorts : Ports (Ty Unit) := Theta.BodyResults dataPorts
private abbrev args : Ports (Ty Unit) := .control 2 :: dataPorts
private abbrev NoPure : Dialect Unit Unit := fun _ _ => Empty

private inductive Mode where
  | stop
  | block
  | restart
  deriving DecidableEq

private inductive Effect : Dialect Unit Unit where
  | step (mode : Mode) : Effect dataPorts bodyPorts

private abbrev value : Unit → Type := fun _ => Nat
private abbrev dataOnly : Data dataPorts := .value .nil
private abbrev bodyData : Data bodyPorts := .control dataOnly
private abbrev argsData : Data args := .control dataOnly

private def data (n : Nat) : Tuple (Values value) dataPorts := .cons n .nil

private def model : Model NoPure Effect Nat where
  value := value
  runPure op := nomatch op
  effect
    | .step mode, .cons n .nil => StateT.mk fun store =>
      if mode = .block ∧ store = 8 then Part.none
      else
        let tag : Fin 2 := if mode = .stop ∧ store = 8 then 0 else 1
        Part.some (.cons ⟨tag⟩ (data ((show Nat from n) + 1)), store + 3)

private abbrev Region {i o : Ports (Ty Unit)} (a : Data i) (b : Data o)
    (sigs : List (Ports (Ty Unit))) :=
  Σ t : Term (Opcode NoPure Effect) (Threaded i) [] sigs (Threaded o),
    ExplicitRuntime.EntryChecked (a := a) (b := b) t

private def body (mode : Mode) : Region dataOnly bodyData [Threaded bodyPorts] :=
  ⟨_, .primitive (.arg (runtimePort dataPorts)) dataOnly bodyData (.effect (.step mode))
    (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] bodyPorts)
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def loop (mode : Mode) : Region dataOnly dataOnly [Threaded dataPorts] :=
  ⟨_, .theta (.arg (runtimePort dataPorts)) dataOnly (.cons (.arg .head) .nil) [Threaded bodyPorts]
    (children := fun _ => (body mode).1) (fun _ => (body mode).2)
    (.ret (nextRuntime [] dataPorts) (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def arms (mode : Mode) (tag : Fin 2) :
    Region dataOnly dataOnly (Fin.cases [Threaded dataPorts] (fun _ => []) tag) :=
  Fin.cases (loop mode)
    (fun _ => ⟨_, .ret (.arg (runtimePort dataPorts)) (.cons (.arg .head) .nil)⟩) tag

private def program (mode : Mode) : Region argsData dataOnly [Threaded dataPorts] :=
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort args)) dataOnly dataOnly
    (.cons (.arg (.tail .head)) .nil) (Fin.cases [Threaded dataPorts] (fun _ => []))
    (children := fun j => (arms mode j).1) (fun j => (arms mode j).2)
    (.ret (nextRuntime [] dataPorts) (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def point (n token : Nat) : Tuple (RuntimeValues value Nat) (Threaded dataPorts) :=
  decode (data n, token)

private def entry (arm : Fin 2) : Tuple (RuntimeValues value Nat) (Threaded args) :=
  .cons ⟨arm⟩ (point 0 2)

private def tagged (tag : Fin 2) (n token : Nat) :
    Tuple (RuntimeValues value Nat) (Threaded bodyPorts) :=
  .cons ⟨tag⟩ (point n token)

private abbrev graph (mode : Mode) := (program mode).1.toGraph
private abbrev admitted (mode : Mode) := (program mode).2.collect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem completes (mode : Mode) (n token : Nat) (tag : Fin 2)
    (result : (model.effect (.step mode) (data n)).run token =
      Part.some (.cons ⟨tag⟩ (data (n + 1)), token + 3)) :
    NestedTheta.Partial.exec (wireModel model) (body mode).1 (point n token) PUnit.unit
      (tagged tag (n + 1) (token + 3)) := by
  refine ⟨tagged tag (n + 1) (token + 3), ?_, ?_⟩
  · change tagged tag (n + 1) (token + 3) ∈
      (wireModel model).primitive (.ordered dataOnly bodyData (.effect (.step mode))) (point n token)
    rw [primitive_mem_iff]
    change (.cons ⟨tag⟩ (data (n + 1)), token + 3) ∈ (model.effect (.step mode) (data n)).run token
    rw [result]
    exact Part.mem_some _
  · rfl

private theorem returns :
    NestedTheta.Partial.returns (wireModel model) (graph .stop) (entry 0) (point 3 11) := by
  rw [NestedTheta.Partial.returns, Term.toTerm_toGraph]
  refine ⟨point 3 11, ⟨point 3 11, ?_, rfl⟩, rfl⟩
  refine Theta.Iterate.again (next := point 1 5) ?_
    (Theta.Iterate.again (next := point 2 8) ?_ (Theta.Iterate.stop ?_))
  · exact completes .stop 0 2 1 rfl
  · exact completes .stop 1 5 1 rfl
  · exact completes .stop 2 8 0 rfl

example : observeErased model (graph .stop) (admitted .stop) (entry 0) =
    Part.some (withRuntime PUnit.unit (data 3), 11) :=
  Part.eq_some_iff.mpr ((returns_iff model _ _ _ _).mp returns)

private def failedAttempt : Observation model :=
  .blocked (attempt model [(0, 0), (0, 0)] 0 (.step .block) (point 2 8))

private theorem blocked : abnormal model (graph .block) (entry 0) failedAttempt := by
  rw [abnormal, Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  refine ⟨point 2 8, (Relation.ReflTransGen.single (b := point 1 5) ?_).tail ?_, ?_⟩
  · exact completes .block 0 2 1 rfl
  · exact completes .block 1 5 1 rfl
  · apply Or.inl
    refine ⟨?_, rfl⟩
    change ¬ False
    exact id

-- Both successful feedback steps pass the updated token. The attempted
-- third step uses the carried payload 2 and token 8 at the selected site.
example : OrderedState.Partial.abnormal (erasedModel model) (admitted .block).erase.toGraph
    (boundaryResult (entry 0)).1 (boundaryResult (entry 0)).2
    (.blocked ⟨[(0, 0), (0, 0)], 0, Threaded dataPorts, Threaded bodyPorts, .op (.step .block),
      withRuntime PUnit.unit (data 2), 8⟩) :=
  (abnormal_iff model _ _ _ failedAttempt).mp blocked

private theorem productive : abnormal model (graph .restart) (entry 0) .diverges := by
  rw [abnormal, Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inr
  refine ⟨rfl, fun n => point n (2 + 3 * n), rfl, ?_⟩
  intro n
  simp only [Nat.mul_succ, ← Nat.add_assoc]
  exact completes .restart n (2 + 3 * n) 1 rfl

example : OrderedState.Partial.abnormal (erasedModel model) (admitted .restart).erase.toGraph
    (boundaryResult (entry 0)).1 (boundaryResult (entry 0)).2 .diverges :=
  (abnormal_iff model _ _ _ .diverges).mp productive

example : ¬ abnormal model (graph .block) (entry 0) .diverges := by
  intro divergent
  have bad := (abnormal_iff model _ (admitted .block) _ failedAttempt).mp blocked
  have infinite := (abnormal_iff model _ (admitted .block) _ .diverges).mp divergent
  cases OrderedState.Partial.abnormal_unique _ _ _ _ bad infinite

-- Selecting the other γ arm leaves the token unchanged and avoids the failing body.
example : observeErased model (graph .block) (admitted .block) (entry 1) =
    Part.some (withRuntime PUnit.unit (data 0), 2) := by
  apply Part.eq_some_iff.mpr
  apply (returns_iff model _ _ _ (point 0 2)).mp
  rw [NestedTheta.Partial.returns, Term.toTerm_toGraph]
  exact ⟨point 0 2, rfl, rfl⟩

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Tests
