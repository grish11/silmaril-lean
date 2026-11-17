module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.Explorer.Defs

/-!
# C functions and their machine code as compilation problems

The instance of `Silmaril.Compiler.Explorer` for the C functions of
`Silmaril.Project.CompilesTo` (`docs/projects/compiles-to.md`): the source is the Cerberus Core
run of a function (`FnData.source`), the target an x86-64 model running its bytes, the entry
convention the System V call (`FnData.Holds … .entry`), and the mapping the function's program
points (`FnData.corr`).

* `FnData.compilation I k0`: the compilation problem (no mapping in it);
* `FnData.mapping I k0`: the segment mapping whose correspondence is `FnData.corr I k0`;
* `coreObjects`, `frameSlots`, `dwarf`: the observation logics of C objects in Core and of frame
  slots on the machine, and the comorphism that reads each C object at its DWARF location
  (`DW_OP_fbreg off`, `size` bytes, frame base the CFA). This is what a debugger does with the
  compiler's debug information; `FnData.scope k` is the objects with a value at point `k`.

The theorems (`Thms`) connect them: every segment proved gives the problem
(`FnData.compilation_valid_of_segments`), and, separately, the mapping's relation refines the
relation `dwarf` generates at every point (`FnData.refines_dwarf`).

The source logic is not functional (`Locals.Slot` fixes the four bytes of an integer, not the
integer), so the refinement gives *a* value that both the Core object and its slot hold, not
equality of every value read.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.Explorer
open Silmaril.Cerberus.Core.Dynamics

/-- **C objects as Core sees them**: an observable is a C object (`Slot`: only its symbol is
read here), and in a Core state whose control runs in the environment `env`, the object holds
`n` when its symbol is bound to an allocated pointer whose `int` slot holds `n` in the Core
memory (`Silmaril.Compile.Core.Verified.Locals.Slot`). -/
def coreObjects : ObsLogic State Int where
  Obs := Slot
  Holds s o n := ∃ E env, s.control = .effectExpr E env ∧ ∃ id addr : Int,
    env.lookup o.sym = some (.object (.pointer (.allocated id addr))) ∧
      Silmaril.Compile.Core.Verified.Locals.Slot s.memory id addr n

/-- A frame-relative machine location: `size` bytes at `off` from the CFA (`DW_OP_fbreg off`,
frame base `DW_OP_call_frame_cfa`). -/
structure FrameLoc where
  off : Int
  size : Nat
  deriving Repr, DecidableEq

/-- **Frame slots as the machine holds them**: in the state `m` of the call entered in `m0`, the
location holds `n` when its bytes are the little-endian bytes of `n` (`SlotHolds`). -/
def frameSlots : ObsLogic (MState × MState) Int where
  Obs := FrameLoc
  Holds p l n :=
    Silmaril.X86.Ext.HoldsLE p.2.memory ((cfa p.1 + l.off).toNat) l.size (BitVec.ofInt 64 n)

/-- **The DWARF comorphism**: each C object is read at its DWARF frame location. -/
def dwarf : ObsComorphism coreObjects frameSlots := ⟨fun o => ⟨o.off, o.size⟩⟩

namespace FnData

variable (F : FnData)

/-- **The compilation problem of a function** on the model `I`, in the caller's continuation
`k0`: the Core run of the procedure, the machine running its bytes, the System V call as entry
convention, the return (`Returned`) and the System V result (`FnData.Result`). -/
def compilation (I : Model) (k0 : List Frame) : Problem State MState Val where
  src := F.source k0
  tgt := I.step
  entry x0 s := F.Holds k0 .entry x0 s x0
  tgtFinal := Returned
  result := F.Result

/-- **The function's segment mapping**: its program points (`FnData.corr`). -/
def mapping (I : Model) (k0 : List Frame) : Mapping (F.compilation I k0) where
  srcAt := (F.corr I k0).srcAt
  tgtAt := (F.corr I k0).tgtAt
  rel := (F.corr I k0).rel

/-- The C objects with a value at point `k` (none at the entry and the return label). -/
def scope (k : Nat) (o : Slot) : Prop :=
  ∃ p, F.points[k]? = some p ∧ ∃ c objs, p.kind = .slots c objs ∧ o ∈ objs ∧ o.defined = true

end FnData

end Silmaril.Project.CompilesTo

end
