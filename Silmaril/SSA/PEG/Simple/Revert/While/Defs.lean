module

public import Silmaril.SSA.PEG.Builder
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

def portEq : {ps : List (Ty Data)} → {out : Ty Data} →
    (a b : Port ps out) → Decidable (a = b)
  | _, _, .head, .head => isTrue rfl
  | _, _, .head, .tail _ => isFalse (by intro h; cases h)
  | _, _, .tail _, .head => isFalse (by intro h; cases h)
  | _, _, .tail a, .tail b =>
    match portEq a b with
    | isTrue h => isTrue (congrArg Port.tail h)
    | isFalse h => isFalse (by intro eq; cases eq; exact h rfl)
termination_by structural _ _ a _ => a

variable {l : Nat} [∀ ins out, DecidableEq (P ins out)]

def labelEq {ins : List (Ty Data)} {out : Ty Data}
    (a b : Label P params (Fin l) ins out) : Decidable (a = b) := by
  cases a <;> cases b
  case param.param a b =>
    letI := portEq a b
    if h : a = b then exact isTrue (congrArg Label.param h)
    else exact isFalse (by intro eq; cases eq; exact h rfl)
  case op.op a b =>
    if h : a = b then exact isTrue (h ▸ rfl) else exact isFalse (by
      intro eq
      cases eq
      exact h rfl)
  case phi.phi => exact isTrue rfl
  case theta.theta a b => exact decidable_of_iff (a = b) (by simp)
  case eval.eval a b => exact decidable_of_iff (a = b) (by simp)
  case pass.pass a b => exact decidable_of_iff (a = b) (by simp)
  all_goals exact isFalse (by intro h; cases h)

def rowEq [DecidableEq Data] {out : Ty Data}
    (a b : RawNode P params l out) : Decidable (a = b) := by
  obtain ⟨ins, label, args⟩ := a
  obtain ⟨ins', label', args'⟩ := b
  if hi : ins = ins' then
    subst ins'
    letI := labelEq label label'
    if hl : label = label' then
      if ha : args = args' then exact isTrue (by subst label'; subst args'; rfl)
      else exact isFalse (fun h => ha (congrArg RawNode.args h))
    else exact isFalse (by intro h; cases h; exact hl rfl)
  else exact isFalse (fun h => hi (congrArg RawNode.inputs h))

/-- Exact serialized equality for a numbered table, including loop IDs and parents. -/
def tableEq [DecidableEq Data] (a b : RawGraph P params results n l) : Decidable (a = b) := by
  obtain ⟨⟨forest⟩, sort, node, roots⟩ := a
  obtain ⟨⟨forest'⟩, sort', node', roots'⟩ := b
  if hf : ∀ i, forest i = forest' i then
    have he := funext hf
    subst forest'
    if hs : ∀ i, sort i = sort' i then
      have he := funext hs
      subst sort'
      letI (i : Fin n) := rowEq (node i) (node' i)
      if hn : ∀ i, node i = node' i then
        have he := funext hn
        subst node'
        if hr : roots = roots' then exact isTrue (by subst roots'; rfl)
        else exact isFalse (fun h => hr (congrArg RawGraph.roots h))
      else exact isFalse (by intro h; cases h; exact hn fun _ => rfl)
    else exact isFalse (by intro h; cases h; exact hs fun _ => rfl)
  else exact isFalse (by intro h; cases h; exact hf fun _ => rfl)

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
