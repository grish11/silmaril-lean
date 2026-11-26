module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.PEG.Bridge.ForwardCFG.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Defs

/-! # Checked PEG loops as named mutable λRTL CFGs -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL

open RVSDG (Port Tuple)
open ForwardCFG (Value)
open Silmaril.SSA.LambdaRTL (Val Model CFG upd obs)
open Silmaril.SSA.LambdaRTL.CFG (Term Body)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic (runFuel run toPartModel)
open Simple.Revert.While.Region (Schedule)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars outs : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1}

/-- The mutable packet, unpacked arguments, and primitive results have
disjoint register names. Suffixes are scratch for pair elimination. -/
inductive Register
  | packet
  | slot (i : Nat)
  | suffix (i : Nat)
  | temp (i : Nat)
  | ignored
  deriving DecidableEq

inductive Label
  | before
  | after
  | exit
  deriving DecidableEq

/-- Keep the existing ordered primitive profiles. The right constructor is
a Boolean-to-sum test for the ordinary λRTL case terminator. -/
abbrev Instruction (P : InstructionSet.{0,0} Data) := ForwardCFG.Instruction P ⊕ Unit

abbrev Store (m : TotalModel P) := Register → Value m.toPEG.Value

def model (m : TotalModel P) [DecidableEq Data] : Model (Instruction P) Option (Value m.toPEG.Value) :=
  let base := ForwardCFG.model m
  { unit := base.unit
    pair := base.pair
    inl := base.inl
    inr := base.inr
    unpair := base.unpair
    split := base.split
    abort := base.abort
    app
      | .inl op, args => base.app op args
      | .inr (), .atom .bool flag => some (if flag.down then .inr .unit else .inl .unit)
      | .inr (), _ => none }

namespace Compiler

abbrev Layout (vars : List (Ty Data)) := ∀ {t}, Port vars t → Register

def initial (offset : Nat) : Layout vars :=
  fun p => .slot (offset + ForwardCFG.Compiler.portIndex p)

def push (layout : Layout vars) (next : Nat) : Layout (t :: vars)
  | _, .head => .temp next
  | _, .tail p => layout p

def operands (layout : Layout vars) : {outs : List (Ty Data)} → Tuple (Port vars) outs → Val Register
  | _, .nil => .unit
  | _, .cons p ps => .pair (.var (layout p)) (operands layout ps)

def packet (layout : Layout vars) : Val Register :=
  operands layout (Simple.ports vars)

/-- The block reads its single packed argument with native pair
elimination. All original slots stay live until the next branch. -/
def unpack (body : Body Register Label (Instruction P)) :
    List (Ty Data) → Nat → Register → Body Register Label (Instruction P)
  | [], _, _ => body
  | _ :: ts, i, src =>
    .let2 (.slot i) (.suffix i) (.val (.var src)) (unpack body ts (i + 1) (.suffix i))

/-- Every certified producer emits a single native assignment to a fresh
temporary. The terminator packs the output wires in the certificate's order. -/
def emit {roots : Tuple (Ref g.sort) outs} :
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
    Schedule g false roots scope → Layout vars → Nat →
    (Layout outs → Term Register Label (Instruction P)) → Body Register Label (Instruction P)
  | _, _, .done reads, layout, _, finish => .term (finish (fun p => layout (reads.slots.get p)))
  | _, _, .bind _ op _ _ _ reads rest, layout, next, finish =>
    .let1 (.temp next) (.app (.inl ⟨_, _, .primitive op⟩) (operands layout reads.slots))
      (emit rest (push layout next) (next + 1) finish)
  | _, _, .branch enabled .., _, _, _ => nomatch enabled

end Compiler

variable {g' : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
variable (b : Bundle g' slot invariants)

def before : Body Register Label (Instruction P) :=
  Compiler.unpack (Compiler.emit b.scalar.guard (Compiler.initial 0) 0 fun outputs =>
    let old := Compiler.packet (fun p => outputs (.tail p))
    .case (.app (.inr ()) (.var (outputs .head))) .ignored (.br .exit old) .ignored (.br .after old))
    carried 0 .packet

def after : Body Register Label (Instruction P) :=
  Compiler.unpack (Compiler.emit b.scalar.update (Compiler.initial 0) 0 fun outputs =>
    .br .before (Compiler.packet outputs)) carried 0 .packet

/-- Full-table lookup follows the after-to-before branch. The exit label
is absent from the table and returns its packet. -/
def lower : CFG Register Label (Instruction P) :=
  ⟨.term (.br .before (.var .packet)), [(.before, ⟨.packet, before b⟩), (.after, ⟨.packet, after b⟩)]⟩

def inputStore (m : TotalModel P) (input : Tuple m.toPEG.Value carried) : Store m :=
  upd (fun _ => .unit) .packet (Value.pack input)

/-- Observe the external label and ordered payload of the bounded mutable
runner, projecting away its scratch register assignments. -/
def observeFuel (m : TotalModel P) [DecidableEq Data] (fuel : Nat) (input : Tuple m.toPEG.Value carried) :
    Option (Label × Value m.toPEG.Value) :=
  (runFuel (model m) (lower b) fuel (inputStore m input)).map obs

noncomputable def observe (m : TotalModel P) [DecidableEq Data] (input : Tuple m.toPEG.Value carried) :
    Part (Label × Value m.toPEG.Value) :=
  obs <$> run (toPartModel (model m)) (lower b) (inputStore m input)

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL
