module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Thms
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner vars : List (Ty Data)} {result : Ty Data}
variable {form : Form P outer inner result}
variable {g : Graph P outer [result] form.size form.size}

theorem compile_eq [DecidableEq Data] (cert : Certificate form g) :
    form.compile = g :=
  (Graph.eq_of_toRaw_eq cert.table).symm

variable {m : Interpretation.{u,v,w} P}

private theorem runWhile_exec {test : Expr P vars .bool} {body : Stmt P true vars vars}
    {step : Tuple m.Value vars → Option (Tuple m.Value vars)}
    (stepExec : ∀ {old next}, step old = some next → Exec m body old (some next))
    (fuel : Nat) {store final : Tuple m.Value vars}
    (success : runWhile m test step fuel store = some final) :
    Exec m (.while rfl test body) store (some final) := by
  rw [runWhile.eq_def] at success
  cases tested : test.eval m store with
  | none => simp [tested] at success
  | some flag =>
    obtain ⟨flag⟩ := flag
    cases flag
    · have same : store = final := by simpa [tested] using success
      subst final
      exact .whileStop tested
    · cases fuel with
      | zero => simp [tested] at success
      | succ fuel =>
        have ran : (step store).bind (runWhile m test step fuel) = some final := by
          simpa [tested] using success
        obtain ⟨next, stepped, rest⟩ := Option.bind_eq_some_iff.mp ran
        exact .whileStep tested (stepExec stepped) (runWhile_exec stepExec fuel rest)
termination_by fuel

private theorem body_exec {old next : Tuple m.Value outer} {final : Tuple m.Value inner}
    (child : Exec m form.child (form.capture m old) (some final))
    (commit : form.commit.runLoopFree m final = some next) :
    Exec m form.body old (some next) :=
  .seq (next := form.capture m old) .project
    (.seq child (commit ▸ form.commit.runLoopFree_enableWhile final))

theorem stepTotal (total : form.Total m) (old : Tuple m.Value outer)
    (test : form.outerGuard.eval m old = some ⟨true⟩) :
    ∃ next, Exec m form.body old (some next) := by
  obtain ⟨final, child⟩ := total.child old test
  obtain ⟨next, commit⟩ := total.commit child
  exact ⟨next, body_exec child commit⟩

private theorem stepFuel_exec (form : Form P outer inner result) (fuel : Nat)
    {old next : Tuple m.Value outer} (success : form.stepFuel m fuel old = some next) :
    Exec m form.body old (some next) := by
  obtain ⟨final, child, commit⟩ := Option.bind_eq_some_iff.mp success
  have childExec : Exec m form.child (form.capture m old) (some final) :=
    runWhile_exec (fun h => h ▸ form.innerStep.runLoopFree_enableWhile _) fuel child
  exact body_exec childExec commit

theorem runFuel_returns (form : Form P outer inner result) (outerFuel innerFuel : Nat)
    (input : Tuple m.Value outer) {value : m.Value result}
    (success : form.runFuel m outerFuel innerFuel input = some value) :
    form.source.Returns m input value := by
  obtain ⟨final, ran, returned⟩ := Option.map_eq_some_iff.mp success
  exact ⟨final, runWhile_exec (stepFuel_exec form innerFuel) outerFuel ran, returned⟩

theorem trace_of_defined [DecidableEq Data] (cert : Certificate form g)
    (input : Tuple m.Value outer) (total : form.Total m)
    (neg : ∀ b : Bool, m.run form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (wf : WellFounded g.Demand) (i : Index form.size) {value : m.Value result}
    (defined : g.observe m (g.denote m input wf) i = .cons (some value) .nil) :
    ∃ k final, WhileTrace m form.outerGuard form.body k input final ∧
      final.get form.returnSlot = value := by
  have eq := compile_eq cert
  subst g
  exact Structured.translate_while_trace_of_defined form.outerGuard form.body form.returnSlot
    form.negate m input neg total.guard (stepTotal total) i defined

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Proofs
