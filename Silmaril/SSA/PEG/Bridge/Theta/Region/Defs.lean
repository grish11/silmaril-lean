module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
public import Silmaril.SSA.RVSDG.Theta.Defs

/-! # Checked PEG loop schedules as structured RVSDG θ bodies -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region

open RVSDG (Origin Port Tuple Wires)
open Simple.Revert.While.Region (Certificate Schedule Reads)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars outs ins : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}

inductive Opcode (P : InstructionSet.{0,0} Data) : RVSDG.Dialect (Ty Data) PUnit
  | primitive {ins out} (op : P ins out) : Opcode P (valuePorts ins) (valuePorts [out])
  | branch : Opcode P (valuePorts [.bool]) [.control 2]

/-- The descriptor's guard is a continuation test. True selects the update
arm, while PEG pass tests the negated guard. No primitive uses a state port. -/
def evalOpcode (m : TotalModel P) {snapshot : PUnit → Type} {ins outs : List (ValuePort Data)} :
    Opcode P ins outs → Tuple (RVSDG.PortType.Val m.toPEG.Value snapshot) ins →
      Tuple (RVSDG.PortType.Val m.toPEG.Value snapshot) outs
  | .primitive op, input => .cons (m.run op (fromPorts _ input)) .nil
  | .branch, .cons flag .nil => .cons ⟨if flag.down then 1 else 0⟩ .nil

abbrev model (m : TotalModel P) : RVSDG.Model (Opcode P) where
  value := m.toPEG.Value
  state _ := PEmpty
  run := evalOpcode m

abbrev encode (m : TotalModel P) (xs : Tuple m.toPEG.Value vars) :
    Tuple (model m).Val (valuePorts vars) := toPorts (F := (model m).Val) xs

/-- Remove the cached continuation flag from the reversion schedule's result. -/
def carriedValues {F : Ty Data → Type} : Tuple F (.bool :: vars) → Tuple F vars
  | .cons _ values => values

namespace Compiler

variable {past : List (List (ValuePort Data))}
variable {t : Ty Data}

abbrev Scope (entry vars : List (Ty Data)) (past : List (List (ValuePort Data))) :=
  ∀ {t}, Port vars t → Origin (valuePorts entry) past (.value t)

def Scope.initial : Scope carried carried past :=
  fun p => .arg (portToValue p)

def Scope.push (scope : Scope carried vars past) :
    Scope carried (t :: vars) (past ++ [valuePorts [t]])
  | _, .head => Bridge.Compiler.newest past t
  | _, .tail p => Bridge.Compiler.weaken _ (scope p)

def wires (scope : Scope carried vars past) :
    {ts : List (Ty Data)} → Tuple (Port vars) ts →
      Wires (valuePorts carried) past (valuePorts ts)
  | _, .nil => .nil
  | _, .cons p ps => .cons (scope p) (wires scope ps)

def args (carried : List (Ty Data)) (past : List (List (ValuePort Data))) :
    Wires (valuePorts carried) past (valuePorts carried) :=
  wires Scope.initial (Simple.ports carried)

def last {entry head : List (ValuePort Data)} {t : ValuePort Data}
    (past : List (List (ValuePort Data))) (p : Port head t) :
    Origin entry (past ++ [head]) t :=
  .output ⟨past.length, by simp⟩ (by simpa using p)

def primitive (op : P ins t) (inputs : Wires (valuePorts carried) past (valuePorts ins)) :
    RVSDG.Node (Opcode P) (valuePorts carried) past (valuePorts [t]) :=
  ⟨_, .simple (.primitive op), inputs, Fin.elim0⟩

abbrev Code (P : InstructionSet.{0,0} Data) (carried : List (Ty Data))
    (past : List (List (ValuePort Data))) (results : List (ValuePort Data)) :=
  Σ sigs, RVSDG.Term (Opcode P) (valuePorts carried) past sigs results

/-- Each checked primitive becomes one RVSDG vertex. The initial scope maps
all θ slots to the old tuple, and a binding adds a new origin without
changing any existing origin. -/
def slice {roots : Tuple (Ref g.sort) outs} {results : List (ValuePort Data)} :
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
    Schedule g false roots scope → {past : List (List (ValuePort Data))} → Scope carried vars past →
      (∀ {past'}, Wires (valuePorts carried) past' (valuePorts outs) → Code P carried past' results) →
      Code P carried past results
  | _, _, .done reads, _, layout, finish => finish (wires layout reads.slots)
  | _, _, .bind _ op _ _ _ reads tail, _, layout, finish =>
    let rest := slice tail layout.push finish
    ⟨_ :: rest.1, .bind (primitive op (wires layout reads.slots)) (fun j => j.elim0) rest.2⟩
  | _, _, .branch enabled _ _ _ _ _ _ _ _ _ _ _, _, _, _ => nomatch enabled

def continueArm (cert : Certificate g allowInvariant) :
    Code P carried [] (valuePorts carried) :=
  slice cert.update Scope.initial (fun outputs => ⟨[], .ret outputs⟩)

def branchNode (flag : Origin (valuePorts carried) past (.value .bool)) :
    RVSDG.Node (Opcode P) (valuePorts carried) past [.control 2] :=
  ⟨_, .simple .branch, .cons flag .nil, Fin.elim0⟩

def selectNode (cert : Certificate g allowInvariant)
    (old : Wires (valuePorts carried) past (valuePorts carried)) :
    RVSDG.Node (Opcode P) (valuePorts carried) (past ++ [[.control 2]]) (valuePorts carried) :=
  ⟨_, .gamma 0, .cons (last past .head) (old.map fun _ w => Bridge.Compiler.weaken _ w),
    Fin.cases [] (fun _ => (continueArm cert).1)⟩

def selectArm (cert : Certificate g allowInvariant)
    (old : Wires (valuePorts carried) past (valuePorts carried)) :
    RVSDG.Children (RVSDG.Term (Opcode P)) (selectNode cert old) :=
  Fin.cases (motive := fun j => RVSDG.Term (Opcode P) (valuePorts carried) []
    ((selectNode cert old).childSigs j) (valuePorts carried))
    (.ret (args carried [])) (fun _ => (continueArm cert).2)

def select (cert : Certificate g allowInvariant)
    (flag : Origin (valuePorts carried) past (.value .bool))
    (old : Wires (valuePorts carried) past (valuePorts carried)) :
    Code P carried past (RVSDG.Theta.BodyResults (valuePorts carried)) :=
  let tagPast := past ++ [[.control 2]]
  let tag := Bridge.Compiler.weaken (valuePorts carried) (last (head := [.control 2]) past .head)
  let payload := wires (fun p => last tagPast (portToValue p)) (Simple.ports carried)
  ⟨[[.control 2], valuePorts carried],
    .bind (branchNode flag) (fun j => j.elim0)
      (.bind (selectNode cert old) (selectArm cert old) (.ret (.cons tag payload)))⟩

def guardFinish (cert : Certificate g allowInvariant)
    (outputs : Wires (valuePorts carried) past (valuePorts (.bool :: carried))) :
    Code P carried past (RVSDG.Theta.BodyResults (valuePorts carried)) :=
  match outputs with | .cons flag old => select cert flag old

def body (cert : Certificate g allowInvariant) :
    Code P carried [] (RVSDG.Theta.BodyResults (valuePorts carried)) :=
  slice cert.guard Scope.initial (guardFinish cert)

end Compiler

/-- Lower an existing checked single-loop PEG, retaining the ordered carried
boundary. The return slot selects the scalar that its PEG eval root samples. -/
def compile (cert : Certificate g allowInvariant) :
    RVSDG.Theta.Graph (Opcode P) (valuePorts carried) (Compiler.body cert).1 :=
  (RVSDG.Theta.Term.mk (Compiler.body cert).2).toGraph

end Silmaril.SSA.PEG.Bridge.Theta.Region
