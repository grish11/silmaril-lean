module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Mathlib.Logic.Equiv.Defs

/-! Reindex the external inputs of a guarded row at the preheader. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires renameVertex)

/-- An old external slot reads a new slot of the same word sort.
The target interface defaults to the original width. -/
abbrev InputMap (arity : Nat) (target : Nat := arity) := Fin arity → Fin target

abbrev InputPermutation (arity : Nat) := Fin arity ≃ Fin arity

universe w

variable {arity : Nat}

/-- An old input address names its image in the new interface. An invalid
raw address remains invalid, so reindexing cannot repair a bad spec. -/
abbrev InputPermutation.index (perm : InputPermutation arity) : Nat → Nat :=
  renameVertex perm

def Spec.reindexInputs (spec : Spec) (perm : InputPermutation arity) : Spec :=
  { spec with entry := spec.entry.map perm.index }

namespace InputPermutation

def slot : {n : Nat} → {t : PortTy} → Port (wordPorts n) t → Fin n
  | _ + 1, _, .head => 0
  | _ + 1, _, .tail port => (slot port).succ

theorem slot_argumentPort : ∀ {n : Nat} (i : Fin n), slot (argumentPort n i) = i
  | 0, i => i.elim0
  | n + 1, i => Fin.cases (motive := fun j => slot (argumentPort (n + 1) j) = j)
      rfl (fun j => congrArg Fin.succ (slot_argumentPort j)) i

theorem slotSort : {n : Nat} → {t : PortTy} → Port (wordPorts n) t → t = wordPort
  | _ + 1, _, .head => rfl
  | _ + 1, _, .tail port => slotSort port

def pullTuple {F : PortTy → Type w} {target : List PortTy} :
    {source : List PortTy} → (∀ {t}, Port source t → Port target t) → Tuple F target → Tuple F source
  | [], _, _ => .nil
  | _ :: _, rename, input =>
      .cons (input.get (rename .head)) (pullTuple (fun p => rename (.tail p)) input)

end InputPermutation

def mapOrigin {source target : List PortTy} {past : List (List PortTy)}
    (map : ∀ {t}, Port source t → Port target t) {t : PortTy} :
    Origin source past t → Origin target past t
  | .arg p => .arg (map p)
  | .output i p => .output i p

/-- Transport argument origins at their declared sorts and keep producer origins. -/
def mapColumn {source target ports : List PortTy} {past : List (List PortTy)}
    (map : ∀ {t}, Port source t → Port target t) (wires : Wires source past ports) :
    Wires target past ports :=
  wires.map fun _ wire => mapOrigin (fun p => map p) wire

namespace InputMap

variable {target : Nat}

/-- Map an external capture address at its original sort. -/
def port (mapping : InputMap arity target) {t : PortTy} (old : Port (wordPorts arity) t) :
    Port (wordPorts target) t :=
  (InputPermutation.slotSort old).symm ▸ argumentPort target (mapping (InputPermutation.slot old))

/-- Map argument origins and keep producer origins in their typed prefix. -/
def column (mapping : InputMap arity target) {ports : List PortTy} {past : List (List PortTy)}
    (wires : Wires (wordPorts arity) past ports) : Wires (wordPorts target) past ports :=
  mapColumn (fun p => mapping.port p) wires

/-- The old valuation reads every old slot at its image in the new tuple. -/
def pull {value : Unit → Type w} (mapping : InputMap arity target)
    (input : Tuple (Val value) (wordPorts target)) : Tuple (Val value) (wordPorts arity) :=
  InputPermutation.pullTuple (fun p => mapping.port p) input

end InputMap

namespace InputPermutation

abbrev port (perm : InputPermutation arity) {t : PortTy} (old : Port (wordPorts arity) t) :
    Port (wordPorts arity) t :=
  InputMap.port (fun i => perm i) old

abbrev column (perm : InputPermutation arity) {ports : List PortTy} {past : List (List PortTy)}
    (wires : Wires (wordPorts arity) past ports) : Wires (wordPorts arity) past ports :=
  InputMap.column (fun i => perm i) wires

abbrev pull {value : Unit → Type w} (perm : InputPermutation arity)
    (input : Tuple (Val value) (wordPorts arity)) : Tuple (Val value) (wordPorts arity) :=
  InputMap.pull (fun i => perm i) input

end InputPermutation

/-- The native typed map is confined to the external entry column. -/
def Plan.reindexInputs (p : Plan arity) (perm : InputPermutation arity) : Plan arity :=
  { p with entry := perm.column p.entry }

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
