module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Elaborates.Thms

/-! # A typing certificate on the φ source

A certificate for a φ graph in the fragment of the elaboration. It
declares a type for every register, the inputs among them, and a type for
every exit label, and it uses the existing typing of primitives. The
check goes through the bodies of the graph:

* a binder of a value or of a primitive has the type of its operand;
* a pattern let binds the two components of a product, and a case binds
  the two sides of a sum;
* a jump to a declared exit carries a payload of the type of the exit;
* on a jump to a block, every φ row of the block takes from this
  predecessor an operand of the declared type of its destination.

Declared types are compared by equality. No register is given a type by
inference, and nothing assumes that a term has one type only.

The type of the packet of a block is computed from the certificate. The
lowering sends on an edge the φ operands of the target, as a right-nested
product in the order of the rows. The versioning adds a record of
registers, in the order of its layout. So the packet type is the product
of the row types and of the types of the record.

The typed elaboration checks the elaborated graph against a packet type
for every block. `Task.certifiedChecks` states that the computed packet
types pass that check for a certified graph; it is open.
-/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row)

universe u v

variable {Base V K : Type u} {F : Type v}

/-- The type of a value under declared register types. -/
def valueType {W : Type u} (types : W → Ty Base) : Val W → Ty Base
  | .var x => types x
  | .unit => .unit
  | .pair a b => .product (valueType types a) (valueType types b)

/-- The right-nested product of the types of a list of registers. -/
def recordType {W : Type u} (types : W → Ty Base) : List W → Ty Base
  | [] => .unit
  | first :: rest => .product (types first) (recordType types rest)

/-- The right-nested product of the destination types of φ rows. -/
def argsType (types : V → Ty Base) : List (Row V K) → Ty Base
  | [] => .unit
  | row :: rest => .product (types row.dst) (argsType types rest)

/-- The declared types on the registers of the lowering. The packet
register has no declared type. -/
def lifted (types : V → Ty Base) : Option V → Ty Base
  | some register => types register
  | none => .unit

/-- The declared types on the names of the normalized graph: a copy has
the type of its register. -/
def forwardTypes (types : V → Ty Base) : Phi.Forward.Name V K → Ty Base :=
  Sum.elim types fun copy => types copy.1

variable [DecidableEq Base] [HasTy F (Ty Base)]

/-- The type of an operand of the fragment, when its argument has the
source type of its primitive. -/
def opType (types : V → Ty Base) : Op V F → Option (Ty Base)
  | .val a => some (valueType types a)
  | .app f a => if valueType types a = instrSrc f then some (instrTrg f) else none
  | .inl _ | .inr _ | .abort _ => none

variable [DecidableEq K]

/-- Check a terminator that the entry or a block `pred` runs. -/
def termTyped (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred : Option K) : Term V (Option K) F → Bool
  | .br target value =>
    match Phi.OrderedExits.lookup graph target with
    | some block => block.rows.all fun row =>
        decide (valueType types (row.operand pred) = types row.dst)
    | none => decide (valueType types value = exitType target)
  | .case operand x left y right =>
    decide (opType types operand = some (.coprod (types x) (types y))) &&
      termTyped graph types exitType pred left && termTyped graph types exitType pred right

/-- Check a body that the entry or a block `pred` runs. -/
def bodyTyped (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred : Option K) : Body V (Option K) F → Bool
  | .let1 x operand rest =>
    decide (opType types operand = some (types x)) && bodyTyped graph types exitType pred rest
  | .let2 x y operand rest =>
    decide (opType types operand = some (.product (types x) (types y))) &&
      bodyTyped graph types exitType pred rest
  | .term tail => termTyped graph types exitType pred tail

/-- The certificate: the entry and every block are typed. -/
def certified (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base) :
    Bool :=
  bodyTyped graph types exitType none graph.entry &&
    graph.blocks.all fun item => bodyTyped graph types exitType (some item.1) item.2.body

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The types of the exits in their declared order. -/
def external (exits : List (Option K)) (exitType : Option K → Ty Base) :
    Fin exits.length → Ty Base :=
  fun i => exitType exits[i]

variable [DecidableEq V]

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The computed type of the packet of a block: its φ operands, and the
record that the versioning of the lowering carries to it. -/
def packetType (graph : Graph V K F) (types : V → Ty Base) (key : K) (block : Block V K F) :
    Ty Base :=
  .product (argsType types block.rows)
    (recordType (lifted types)
      (Versioning.slots (Phi.OrderedExits.lower graph) (Phi.OrderedExits.lowerBlock graph key block)))

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The computed packet types of the blocks, in order. -/
def packets (graph : Graph V K F) (types : V → Ty Base) : List (Ty Base) :=
  graph.blocks.map fun item => packetType graph types item.1 item.2

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The computed packet types at the positions of the elaborated blocks. -/
def internal (graph : Graph V K F) (types : V → Ty Base) :
    Fin (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length → Ty Base :=
  fun i => (packets graph types).getD i.val .unit

omit [DecidableEq Base] [HasTy F (Ty Base)] [DecidableEq V] in
/-- The canonical typing of versioned names: every version of a source
register has the declared type of the register. -/
def canon (types : V → Ty Base) : Option V × Nat → Ty Base :=
  fun name => lifted types name.1

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The type that a jump of the versioned lowering carries to a label: the
computed packet type of a block, or the declared type of another label. -/
def targetType (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base) :
    Option K → Ty Base
  | some key => (graph.blocks.lookup key).elim (exitType (some key)) (packetType graph types key)
  | none => exitType none

omit [DecidableEq V] [DecidableEq K] in
/-- Named typing of a region: one type for every name and one for every
label. A binder has the type of its operand, a pattern let binds the
components of a product, a case binds the sides of a sum, and a jump
carries a value of the type of its label. A name has one type wherever
it is bound, so binding a name again needs no care. -/
def regionTyped {N L : Type u} (ty : N → Ty Base) (labelType : L → Ty Base) :
    Region N L F → Bool
  | .br label value => decide (valueType ty value = labelType label)
  | .let1 x operand rest =>
    decide (opType ty operand = some (ty x)) && regionTyped ty labelType rest
  | .let2 x y operand rest =>
    decide (opType ty operand = some (.product (ty x) (ty y))) && regionTyped ty labelType rest
  | .case operand x left y right =>
    decide (opType ty operand = some (.coprod (ty x) (ty y))) &&
      regionTyped ty labelType left && regionTyped ty labelType right
  | .join _ _ _ _ => false

/-- Open: the elaborated lowering of a certified φ graph passes the typing
check at the computed packet types, when the capture context has the
declared types of the captures. -/
def Task.certifiedChecks (Base V K : Type u) (F : Type v) [DecidableEq Base] [HasTy F (Ty Base)]
    [DecidableEq V] [DecidableEq K] : Prop :=
  ∀ (graph : Graph V K F) (exits : List (Option K)) (types : V → Ty Base)
    (exitType : Option K → Ty Base) {n : Nat} (captures : Fin n → Option V)
    (captureTypes : BoundCtx (Ty Base) n)
    (target : LambdaSSA.FiniteCFG F (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length
      exits.length n),
    certified graph types exitType = true →
    (∀ i, captureTypes.get i = lifted types (captures i)) →
    NamedFlat.compile (Phi.OrderedExits.lower graph) exits captures = some target →
    check target captureTypes (internal graph types) (external exits exitType) = true

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
