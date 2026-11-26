module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG Val upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open Phi.Certified.Entry.OrderedExits.Readback (Provenance packetValue)

/-- Type the structural operand of an existing pure jump. A variable
occurrence takes its type from its position in the destination packet. -/
inductive StructuralSeed {n : Nat} : Val (Fin n) → PacketType → Type 1
  | var (slot : Fin n) (ty : PacketType) : StructuralSeed (.var slot) ty
  | unit : StructuralSeed .unit .unit
  | pair {left right : Val (Fin n)} {a b : PacketType} :
      StructuralSeed left a → StructuralSeed right b → StructuralSeed (.pair left right) (.product a b)

namespace StructuralSeed

variable {n : Nat} {V : Type 1}

def check : (seed : Val (Fin n)) → (ty : PacketType) → Option (StructuralSeed seed ty)
  | .var slot, ty => some (.var slot ty)
  | .unit, .unit => some .unit
  | .pair left right, .product a b => do return .pair (← check left a) (← check right b)
  | _, _ => none

/-- Keep every typed occurrence. A repeated register can have multiple
constraints, all of which must hold for its single value. -/
def footprint (names : Fin n → V) : {seed : Val (Fin n)} → {ty : PacketType} →
    StructuralSeed seed ty → List (V × PacketType)
  | _, _, .var slot ty => [(names slot, ty)]
  | _, _, .unit => []
  | _, _, .pair left right => left.footprint names ++ right.footprint names

/-- Read back the register values required by a particular typed packet. -/
def assignment (names : Fin n → V) : {seed : Val (Fin n)} → {ty : PacketType} →
    StructuralSeed seed ty → Denote ty → List (V × Value Atom)
  | _, _, .var slot ty, packet => [(names slot, PacketType.encode ty packet)]
  | _, _, .unit, _ => []
  | _, _, .pair left right, (a, b) => left.assignment names a ++ right.assignment names b

def captureEnv (names : Fin n → V) (initial : V → Value Atom) : Env Atom :=
  fun i => if h : i < n then initial (names ⟨i, h⟩) else .unit

def reads : Val V → List V
  | .var name => [name]
  | .unit => []
  | .pair left right => reads left ++ reads right

def assignmentStore [DecidableEq V] : List (V × Value Atom) → V → Value Atom
  | [] => fun _ => .unit
  | (name, value) :: tail => upd (assignmentStore tail) name value

end StructuralSeed

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}

/-- Exact named admission and public re-elaboration, with the typed
capture occurrences recovered from the actual erased entry operand. -/
structure StructuralEntry (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K)
    (fields : K → List V) (inputType : PacketType) (outputs : Fin exits.length → PacketType) where
  names : List V
  program : Program signature (fun _ : Fin 1 => inputType) outputs
  entry : Program.PackedEntry program 0
  closed : RoundTrip.PacketClosed (LiveOut.attach fields source)
  flat : FiniteCFG F (LiveOut.attach fields source).blocks.length exits.length names.length
  accepted : NamedFlat.elaborate (LiveOut.attach fields source) exits (fun i => names[i.val]) = some flat
  provenance : Provenance flat entry.target
  typedSeed : StructuralSeed provenance.seed inputType
  publicCaptures : ∀ i, entry.captures i = ⟨0⟩

/-- Infer the source capture layout from the written pure jump, then
check the attached table and its public row readback. -/
def constructStructural [DecidableEq F] (signature : PrimitiveSignature F) (source : CFG V K F)
    (exits : List K) (fields : K → List V) (inputType : PacketType)
    (internal : Fin (LiveOut.attach fields source).blocks.length → PacketType)
    (outputs : Fin exits.length → PacketType) : Option (StructuralEntry signature source exits fields inputType outputs) :=
  match source.entry with
  | .term (.br _ seed) => do
    let names := (StructuralSeed.reads seed).eraseDups
    let attached := LiveOut.attach fields source
    if closed : ∀ i : Fin attached.blocks.length, attached.blocks[i.val].2.body.toRegion.fv ⊆
        {attached.blocks[i.val].2.param} then
      match accepted : NamedFlat.elaborate attached exits (fun i => names[i.val]) with
      | none => none
      | some flat => do
        let built ← Phi.Certified.Entry.OrderedExits.Readback.construct signature internal outputs flat
        if captures : ∀ i, built.packed.captures i = ⟨0⟩ then
          if profile : internal built.start = inputType then
            let typed ← StructuralSeed.check built.provenance.seed (internal built.start)
            let result : StructuralEntry signature source exits fields (internal built.start) outputs :=
              ⟨names, built.program, built.packed, Construction.packetClosed attached closed,
                flat, accepted, built.provenance, typed, captures⟩
            some (profile ▸ result)
          else none
        else none
    else none
  | _ => none

variable (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

def StructuralEntry.footprint : List (V × PacketType) :=
  left.typedSeed.footprint (fun i => left.names[i.val])

def StructuralEntry.evalSeed (initial : V → Value Atom) : Value Atom :=
  packetValue (StructuralSeed.captureEnv (fun (i : Fin left.names.length) => left.names[i.val]) initial)
    left.provenance.seed

def StructuralEntry.assignment (packet : Denote inputType) : List (V × Value Atom) :=
  left.typedSeed.assignment (fun i => left.names[i.val]) packet

/-- Enumerate both typed packets and retain the assignments that give one
value to every shared name, including repeated uses in a single entry. -/
def StructuralEntry.jointAssignments : List (List (V × Value Atom)) :=
  (inputType.enumerate.product rightType.enumerate).filterMap fun (a, b) =>
    let assignment := left.assignment a ++ right.assignment b
    if assignment.all (fun (name, value) => decide (StructuralSeed.assignmentStore assignment name = value))
    then some assignment else none

def StructuralEntry.jointStores : List (V → Value Atom) :=
  (left.jointAssignments right).map StructuralSeed.assignmentStore

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
