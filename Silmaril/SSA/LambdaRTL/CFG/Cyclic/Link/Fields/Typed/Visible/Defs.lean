module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.List.ProdSigma

/-! Finite weak trace checking for structural packets with label-indexed types. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (Tree vis diverge)
open Silmaril.Elgot.ITree.Finite (Event Head Step)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel treeExitNumber)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Primitive)

abbrev PacketType := Ty Empty
def Denote : PacketType → Type
  | .base x => x.elim
  | .empty => PEmpty
  | .unit => PUnit
  | .product x y => Prod (Denote x) (Denote y)
  | .coprod x y => Sum (Denote x) (Denote y)
abbrev Atom := PUnit.{2}
abbrev Register := ULift.{1} Nat

namespace PacketType

/-- Enumerate structural packet values, in sum and product order. -/
def enumerate : (ty : PacketType) → List (Denote ty)
  | .base x => x.elim
  | .unit => [⟨⟩]
  | .empty => []
  | .product x y => (enumerate x).product (enumerate y)
  | .coprod x y => (enumerate x).map Sum.inl ++ (enumerate y).map Sum.inr

@[instance_reducible] def finite : (ty : PacketType) → Fintype (Denote ty)
  | .base x => x.elim
  | .unit => inferInstanceAs (Fintype PUnit)
  | .empty => inferInstanceAs (Fintype PEmpty)
  | .product x y =>
    letI := finite x
    letI := finite y
    inferInstanceAs (Fintype (Denote x × Denote y))
  | .coprod x y =>
    letI := finite x
    letI := finite y
    inferInstanceAs (Fintype (Denote x ⊕ Denote y))

def decEq : (ty : PacketType) → DecidableEq (Denote ty)
  | .base x => x.elim
  | .unit => inferInstanceAs (DecidableEq PUnit)
  | .empty => inferInstanceAs (DecidableEq PEmpty)
  | .product x y =>
    letI := decEq x
    letI := decEq y
    inferInstanceAs (DecidableEq (Denote x × Denote y))
  | .coprod x y =>
    letI := decEq x
    letI := decEq y
    inferInstanceAs (DecidableEq (Denote x ⊕ Denote y))

instance (ty : PacketType) : Fintype (Denote ty) := finite ty
instance (ty : PacketType) : DecidableEq (Denote ty) := decEq ty

def encode : (ty : PacketType) → Denote ty → Value Atom
  | .base x, _ => x.elim
  | .unit, _ => .unit
  | .empty, x => x.elim
  | .product x y, (left, right) => .pair (encode x left) (encode y right)
  | .coprod x _, .inl left => .inl (encode x left)
  | .coprod _ y, .inr right => .inr (encode y right)

def decode : (ty : PacketType) → Value Atom → Option (Denote ty)
  | .unit, .unit => some ⟨⟩
  | .product x y, .pair left right => do
    return (← decode x left, ← decode y right)
  | .coprod x _, .inl left => (decode x left).map Sum.inl
  | .coprod _ y, .inr right => (decode y right).map Sum.inr
  | _, _ => none

end PacketType

open PacketType (encode decode)

/-- Each opcode determines its exact finite argument and reply types. -/
structure PrimitiveSignature (F : Type) where
  argument : F → PacketType
  reply : F → PacketType

namespace PrimitiveSignature

variable {F : Type} (signature : PrimitiveSignature F)

abbrev Request := (op : F) × Denote (signature.argument op)
abbrev Reply (key : signature.Request) := Denote (signature.reply key.1)

@[instance_reducible] def typing : HasTy F PacketType := ⟨signature.argument, signature.reply⟩

def primitive : Primitive (Event signature.Request signature.Reply) F Atom := fun op raw =>
  match decode (signature.argument op) raw with
  | some arg => vis (.ask ⟨op, arg⟩) fun reply => pure (encode (signature.reply op) reply)
  | none => diverge

end PrimitiveSignature

variable {Γ rest : List PacketType} {ty head x y : PacketType}

inductive Slot : List PacketType → PacketType → Type where
  | here {ty : PacketType} {rest : List PacketType} : Slot (ty :: rest) ty
  | there {ty head : PacketType} {rest : List PacketType} : Slot rest ty → Slot (head :: rest) ty

/-- Old slots retain their names when fresh binders are added. -/
def Slot.reg : {Γ : List PacketType} → {ty : PacketType} → Slot Γ ty → Register
  | _, _, @Slot.here _ rest => ⟨rest.length⟩
  | _, _, .there slot => Slot.reg slot

abbrev Env (Γ : List PacketType) := ∀ {ty}, Slot Γ ty → Denote ty

def extend (env : Env Γ) (value : Denote ty) : Env (ty :: Γ) :=
  fun {_} slot => match slot with
    | .here => value
    | .there old => env old

def single (value : Denote ty) : Env [ty] :=
  fun {_} slot => match slot with
    | .here => value
    | .there old => nomatch old

inductive Expr (Γ : List PacketType) : PacketType → Type where
  | var {ty : PacketType} : Slot Γ ty → Expr Γ ty
  | unit : Expr Γ .unit
  | pair {x y : PacketType} : Expr Γ x → Expr Γ y → Expr Γ (.product x y)

def Expr.eval (env : Env Γ) : {ty : PacketType} → Expr Γ ty → Denote ty
  | _, .var slot => env slot
  | _, .unit => ⟨⟩
  | _, .pair x y => (Expr.eval env x, Expr.eval env y)

def Expr.compile : {ty : PacketType} → Expr Γ ty → Val Register
  | _, .var slot => .var slot.reg
  | _, .unit => .unit
  | _, .pair x y => .pair (Expr.compile x) (Expr.compile y)

abbrev PacketAt {L : Type} (types : L → PacketType) := (label : L) × Denote (types label)

inductive Branch {L : Type} (types : L → PacketType) : List PacketType → Type where
  | jump {Γ : List PacketType} (label : L) : Expr Γ (types label) → Branch types Γ
  | case {Γ : List PacketType} {x y : PacketType} : Expr Γ (.coprod x y) → Branch types (x :: Γ) → Branch types (y :: Γ) → Branch types Γ

def Branch.transfer {L : Type} {types : L → PacketType} :
    {Γ : List PacketType} → Env Γ → Branch types Γ → PacketAt types
  | _, env, .jump label value => ⟨label, value.eval env⟩
  | _, env, .case value left right =>
    match value.eval env with
    | .inl x => Branch.transfer (extend env x) left
    | .inr y => Branch.transfer (extend env y) right

def Branch.compile {F L : Type} {types : L → PacketType} :
    {Γ : List PacketType} → Branch types Γ → Term Register (ULift.{1} L) F
  | _, .jump label value => .br ⟨label⟩ value.compile
  | Γ, .case value left right =>
    .case (.val value.compile) ⟨Γ.length⟩ (Branch.compile left) ⟨Γ.length⟩ (Branch.compile right)

/-- Pure destructuring precedes a terminator or one visible application.
A primitive continuation repacks the reply and any retained slots for the
chosen label. -/
inductive Code {F L : Type} (signature : PrimitiveSignature F) (types : L → PacketType) : List PacketType → Type where
  | term {Γ : List PacketType} : Branch types Γ → Code signature types Γ
  | unpack {Γ : List PacketType} {x y : PacketType} : Expr Γ (.product x y) → Code signature types (y :: x :: Γ) → Code signature types Γ
  | apply {Γ : List PacketType} (op : F) (arg : Expr Γ (signature.argument op)) (target : L)
      (next : Expr (signature.reply op :: Γ) (types target)) : Code signature types Γ

variable {F L : Type} {signature : PrimitiveSignature F} {types : L → PacketType}

abbrev Action (signature : PrimitiveSignature F) (types : L → PacketType) :=
  ((key : signature.Request) × (signature.Reply key → PacketAt types)) ⊕ PacketAt types

def Code.action : {Γ : List PacketType} → Env Γ → Code signature types Γ → Action signature types
  | _, env, .term branch => .inr (branch.transfer env)
  | _, env, .unpack value tail =>
    let (x, y) := value.eval env
    Code.action (extend (extend env x) y) tail
  | _, env, .apply op arg label next =>
    .inl ⟨⟨op, arg.eval env⟩, fun reply => ⟨label, next.eval (extend env reply)⟩⟩

def Code.compile : {Γ : List PacketType} → Code signature types Γ → Body Register (ULift.{1} L) F
  | _, .term branch => .term branch.compile
  | Γ, .unpack value tail => .let2 ⟨Γ.length⟩ ⟨Γ.length + 1⟩ (.val value.compile) (Code.compile tail)
  | Γ, .apply op arg label next => .let1 ⟨Γ.length⟩ (.app op arg.compile) (.term (.br ⟨label⟩ next.compile))

variable {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}

structure Program (signature : PrimitiveSignature F) (inputs : Fin a → PacketType) (outputs : Fin b → PacketType) where
  locals : Nat
  localType : Fin locals → PacketType
  entry : Fin a → Label locals b
  entryType : ∀ i, Sum.elim localType outputs (entry i) = inputs i
  block : ∀ i, Code signature (Sum.elim localType outputs) [localType i]

namespace Program

variable (program : Program signature inputs outputs)

abbrev Address := ULift.{1} (Label program.locals b)
abbrev State := ULift.{1} (PacketAt (Sum.elim program.localType outputs))
abbrev Result (outputs : Fin b → PacketType) := ULift.{1} (PacketAt outputs)

def states : Finset program.State :=
  (Finset.univ : Finset (PacketAt (Sum.elim program.localType outputs))).map ⟨ULift.up, ULift.up_injective⟩

theorem mem_states (state : program.State) : state ∈ program.states := by
  cases state
  simp [states]

def start (input : Fin a) (packet : Denote (inputs input)) : program.State :=
  ⟨⟨program.entry input, cast (congrArg Denote (program.entryType input).symm) packet⟩⟩

def step (state : program.State) : Step signature.Request (Result outputs) program.State signature.Reply :=
  match state.down with
  | ⟨.inr port, packet⟩ => .inl (.result ⟨⟨port, packet⟩⟩)
  | ⟨.inl index, packet⟩ =>
    match (program.block index).action (single packet) with
    | .inr next => .inr ⟨next⟩
    | .inl ⟨key, next⟩ => .inl (.request key fun reply => ⟨next reply⟩)

def compile (input : Fin a) : CFG Register program.Address F :=
  ⟨.term (.br ⟨program.entry input⟩ (.var ⟨0⟩)),
    (List.finRange program.locals).map fun i => (⟨.inl i⟩, ⟨⟨0⟩, (program.block i).compile⟩)⟩

def exits : List program.Address := (List.finRange b).map fun i => ⟨.inr i⟩

def renderResult (result : Result outputs) : Nat × Value Atom :=
  (result.down.1.val, encode (outputs result.down.1) result.down.2)

def store (input : Fin a) (packet : Denote (inputs input)) : Register → Value Atom :=
  upd (fun _ => .unit) ⟨0⟩ (encode (inputs input) packet)

noncomputable def observe (input : Fin a) (packet : Denote (inputs input)) :
    Tree (Event signature.Request signature.Reply) (Nat × Value Atom) :=
  CFG.Cyclic.runSSA (treeModel.{0, 0} signature.primitive) (program.compile input) (store input packet) >>=
    fun result => pure (treeExitNumber program.exits result)

def refinementAt? [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) : Bool :=
  Silmaril.Elgot.ITree.Finite.compare program.states right.states program.step right.step
    (program.start input packet) (right.start input packet)

def refinement? [DecidableEq F] (right : Program signature inputs outputs) : Bool :=
  decide (∀ input (packet : Denote (inputs input)), program.refinementAt? right input packet = true)

/-- Decide mutual finite weak trace inclusion at one typed input packet. -/
def weakEqAt? [DecidableEq F] (right : Program signature inputs outputs)
    (input : Fin a) (packet : Denote (inputs input)) : Bool :=
  program.refinementAt? right input packet && right.refinementAt? program input packet

/-- Search public entries in order and return an exact typed input that
distinguishes the programs, if any. -/
def firstMismatch? [DecidableEq F] (right : Program signature inputs outputs) : Option (PacketAt inputs) :=
  ((List.finRange a).sigma fun i => PacketType.enumerate (inputs i)).find?
    (fun p => !(program.weakEqAt? right p.1 p.2))

/-- Decide weak tree equality over every entry and its typed packets. -/
def weakEq? [DecidableEq F] (right : Program signature inputs outputs) : Bool :=
  (program.firstMismatch? right).isNone

end Program

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
