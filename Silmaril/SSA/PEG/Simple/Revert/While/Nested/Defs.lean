module

public import Silmaril.SSA.PEG.Simple.Revert.While.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Defs

/-! # Checked reversion of a two-level while

The supplied form has one inner while in the outer update. An ordered
projection captures the old outer store before the call. The child sees
only that vector, and a loop-free commit computes the entire next outer
store from the completed child store. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner vars : List (Ty Data)} {result : Ty Data}

/-- The two loop stores may have different profiles. Copies of old outer
values used after the child must be carried through explicit capture slots. -/
structure Form (P : InstructionSet.{u,v} Data) (outer inner : List (Ty Data))
    (result : Ty Data) where
  outerGuard : Expr P outer .bool
  captures : Tuple (Port outer) inner
  innerGuard : Expr P inner .bool
  innerStep : Stmt P false inner inner
  commit : Stmt P false inner outer
  returnSlot : Port outer result
  negate : P [.bool] .bool

variable (form : Form P outer inner result)

def Form.child : Stmt P true inner inner :=
  .while rfl form.innerGuard form.innerStep.enableWhile

def Form.body : Stmt P true outer outer :=
  .seq (.project form.captures) (.seq form.child form.commit.enableWhile)

def Form.source : Program P true outer result :=
  Structured.whileProgram form.outerGuard form.body form.returnSlot

def Form.size : Nat := (Structured.program form.source form.negate).nodes.length

def Form.compile : Graph P outer [result] form.size form.size :=
  Structured.translate form.source form.negate

/-- Admission evidence compares the entire input table. This includes
the ordered capture wires, child feedback and exit, outer commit wires,
parent table, and designated result. The size is fixed by the form. -/
structure Certificate (form : Form P outer inner result)
    (g : Graph P outer [result] form.size form.size) : Type where
  table : g.toRaw = form.compile.toRaw

/-- Check a supplied nested form against the existing structured compiler's
layout. The comparison validates all references and loop identities. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] form.size form.size) : Option (Certificate form g) :=
  letI := Check.tableEq g.toRaw form.compile.toRaw
  if h : g.toRaw = form.compile.toRaw then some ⟨h⟩ else none

def Certificate.revert {form : Form P outer inner result}
    {g : Graph P outer [result] form.size form.size} (_cert : Certificate form g) :
    Program P true outer result := form.source

variable (m : Interpretation.{u,v,w} P)

def Form.capture (old : Tuple m.Value outer) : Tuple m.Value inner :=
  form.captures.map fun _ slot => old.get slot

/-- The child must terminate successfully on captures of continuing
outer stores. The commit must succeed on the completed child stores. -/
structure Form.Total : Prop where
  guard : ∀ old : Tuple m.Value outer, ∃ b : Bool, form.outerGuard.eval m old = some ⟨b⟩
  child : ∀ old : Tuple m.Value outer, form.outerGuard.eval m old = some ⟨true⟩ →
    ∃ final, Exec m form.child (form.capture m old) (some final)
  commit : ∀ {old : Tuple m.Value outer} {final : Tuple m.Value inner},
    Exec m form.child (form.capture m old) (some final) →
    ∃ next, form.commit.runLoopFree m final = some next

def runWhile (test : Expr P vars .bool)
    (step : Tuple m.Value vars → Option (Tuple m.Value vars)) :
    Nat → Tuple m.Value vars → Option (Tuple m.Value vars)
  | fuel, store => do
    let some flag := test.eval m store | none
    if flag.down then
      match fuel with
      | 0 => none
      | n + 1 => (step store).bind (runWhile test step n)
    else some store
termination_by structural fuel _ => fuel

def Form.stepFuel (innerFuel : Nat) (old : Tuple m.Value outer) : Option (Tuple m.Value outer) := do
  let final ← runWhile m form.innerGuard (form.innerStep.runLoopFree m) innerFuel (form.capture m old)
  form.commit.runLoopFree m final

/-- Fuel bounds outer steps and, independently, the steps of each child invocation. -/
def Form.runFuel (outerFuel innerFuel : Nat) (input : Tuple m.Value outer) :
    Option (m.Value result) :=
  (runWhile m form.outerGuard (form.stepFuel m innerFuel) outerFuel input).map
    fun final => final.get form.returnSlot

end Silmaril.SSA.PEG.Simple.Revert.While.Nested
