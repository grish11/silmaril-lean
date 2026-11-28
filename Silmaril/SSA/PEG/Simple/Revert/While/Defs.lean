module

public import Silmaril.SSA.PEG.Reindex.Defs
public import Silmaril.SSA.PEG.Simple.While.Defs

/-! # Reversion of a canonical one-slot loop

The numbered table is the existing top-level while compiler's output for
a unary guard and unary update. Extraction reads the three primitive
symbols from the table and checks all rows against the recompiled form.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {state : Ty Data} {params results : List (Ty Data)} {n : Nat}

/-- One carried slot, with a continuation test, a feedback update, and
the Boolean negation used for the PEG exit test. -/
structure Form (P : InstructionSet.{u,v} Data) (state : Ty Data) where
  guard : P [state] .bool
  update : P [state] state
  negate : P [.bool] .bool

def Form.program (form : Form P state) : WhileProgram P [state] state :=
  ⟨.op form.guard (.cons (.var .head) .nil),
    .seq (.assign (.op form.update (.cons (.var .head) .nil))) (.project (.cons .head .nil)),
    .head⟩

def Form.compile (form : Form P state) : Graph P [state] [state] 7 1 :=
  form.program.translate form.negate

def castPrimitive [DecidableEq Data] {domain : List (Ty Data)} {range : Ty Data}
    (opcode : P domain range) (ins : List (Ty Data)) (out : Ty Data) : Option (P ins out) :=
  if hi : domain = ins then
    if ho : range = out then some (ho ▸ hi ▸ opcode) else none
  else none

/-- Read an opcode only when its profile matches the requested profile. -/
def readPrimitive [DecidableEq Data] (g : Graph P params results n 1) (i : Fin n)
    (ins : List (Ty Data)) (out : Ty Data) : Option (P ins out) :=
  match (g.node i).label with
  | .op opcode => castPrimitive opcode ins out
  | _ => none

/-- The positions of the exit-test opcode, update, and continuation test
in the existing compiler's numbered output. -/
def probe [DecidableEq Data] (g : Graph P [state] [state] 7 1) : Option (Form P state) := do
  let negate ← readPrimitive g 2 [.bool] .bool
  let update ← readPrimitive g 3 [state] state
  let guard ← readPrimitive g 4 [state] .bool
  return ⟨guard, update, negate⟩

namespace Check

theorem singlePort {out : Ty Data} (a b : Port [state] out) : a = b := by
  cases a with
  | head =>
    cases b with
    | head => rfl
    | tail p => exact nomatch p
  | tail p => exact nomatch p

export RawGraph.Check (portEq labelEq rowEq tableEq)

end Check

structure Certificate (g : Graph P [state] [state] 7 1) where
  form : Form P state
  table : g.toRaw = form.compile.toRaw

/-- Automatically recover the source while from the exact canonical table. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P [state] [state] 7 1) : Option (Certificate g) := do
  let form ← probe g
  letI := Check.tableEq g.toRaw form.compile.toRaw
  if h : g.toRaw = form.compile.toRaw then
    return ⟨form, h⟩
  else none

def Certificate.revert {g : Graph P [state] [state] 7 1} (cert : Certificate g) :
    Program P true [state] state := cert.form.program.source

end Silmaril.SSA.PEG.Simple.Revert.While
