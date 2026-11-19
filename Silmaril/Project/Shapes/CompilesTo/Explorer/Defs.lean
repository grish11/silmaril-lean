module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.Explorer.Det.Defs

/-!
# C functions and their machine code as compilation problems

The instance of `Silmaril.Compiler.Explorer` (through its deterministic specialisation
`Silmaril.Compiler.Explorer.Det`) for the C functions of `Silmaril.Project.CompilesTo`
(`docs/projects/compiles-to.md`):

* `FnData.compilation I k0`: the deterministic problem: the Cerberus Core run of the function
  (`FnData.source`) against the model `I` running its bytes, the System V call as entry
  convention (`FnData.Holds … .entry`), the return (`Returned`) and the System V result
  (`FnData.Result`: callee-saved registers restored, writes only in the frame, the value in
  `rax`). Its generic reading `(F.compilation I k0).toProblem` stops the machine at its first
  return.
* `FnData.mapping I k0`: the cut-point mapping whose correspondence is `FnData.corr I k0`.
* `readCore`, `readFrame`, `dwarf`: Core states and machine states read as models of the
  institutions of value observations (`Silmaril.Compiler.Explorer.obsInst`) over C objects and
  frame locations, and the semi-comorphism of the location map that reads each C object at its
  frame slot (`DW_OP_fbreg off`, `size` bytes, frame base the CFA). `FnData.dwarfRel k` is the
  relation it generates on the objects with a value at point `k` (`FnData.scope`).

What these do not say:

* The slot offsets are the `FnData`'s, which `tools/c-tv` reads from the object's DWARF with an
  unverified reader; no statement here says they are the object's `DW_OP_fbreg` locations.
* The source logic is not functional (`Locals.Slot` fixes four bytes, not an integer), so the
  generated relation is a *witnessed* one: a value both sides hold.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.Explorer
open Silmaril.Cerberus.Core.Dynamics

/-- A frame-relative machine location: `size` bytes at `off` from the CFA. -/
structure FrameLoc where
  off : Int
  size : Nat
  deriving Repr, DecidableEq

/-- **Core states read as valuations of C objects**: in a Core state whose control runs in the
environment `env`, the object `o` (only its symbol is read) holds `n` when its symbol is bound
to an allocation whose `int` slot holds `n` in the Core memory (`Locals.Slot`). -/
def readCore (s : State) : (obsInst Slot Int).Mod obsSig :=
  (fun o n => ∃ E env, s.control = .effectExpr E env ∧ ∃ id addr : Int,
    env.lookup o.sym = some (.object (.pointer (.allocated id addr))) ∧
      Silmaril.Compile.Core.Verified.Locals.Slot s.memory id addr n : Slot → Int → Prop)

/-- **Machine states read as valuations of frame locations**: for the call entered in `p.1`, in
the state `p.2`, a location holds `n` when its bytes are the little-endian bytes of `n`. -/
def readFrame (p : MState × MState) : (obsInst FrameLoc Int).Mod obsSig :=
  (fun l n => Silmaril.X86.Ext.HoldsLE p.2.memory ((cfa p.1 + l.off).toNat) l.size
    (BitVec.ofInt 64 n) : FrameLoc → Int → Prop)

/-- **The location semi-comorphism**: each C object is read at its frame slot. -/
def dwarf : Silmaril.Inst.SemiComorphism (obsInst Slot Int) (obsInst FrameLoc Int) :=
  obsSemi fun o => ⟨o.off, o.size⟩

namespace FnData

variable (F : FnData)

/-- **The compilation problem of a function** on the model `I`, in the caller's continuation
`k0`. -/
def compilation (I : Model) (k0 : List Frame) : DetProblem State MState Val where
  src := F.source k0
  tgt := I.step
  entry x0 s := F.Holds k0 .entry x0 s x0
  tgtFinal := Returned
  result := F.Result

/-- **The function's cut-point mapping**: its program points (`FnData.corr`). -/
def mapping (I : Model) (k0 : List Frame) : DetMapping (F.compilation I k0) where
  srcAt := (F.corr I k0).srcAt
  tgtAt := (F.corr I k0).tgtAt
  rel := (F.corr I k0).rel

/-- The C objects with a value at point `k` (none at the entry and the return label). -/
def scope (k : Nat) (o : Slot) : Prop :=
  ∃ p, F.points[k]? = some p ∧ ∃ c objs, p.kind = .slots c objs ∧ o ∈ objs ∧ o.defined = true

/-- **The relation `dwarf` generates at point `k`**: each object in scope has a value that it
holds in Core and that its frame slot holds on the machine. -/
abbrev dwarfRel (k : Nat) (s : State) (p : MState × MState) : Prop :=
  Gen.Witnessed dwarf obsSig readCore readFrame obsFam (F.scope k) s p

end FnData

/-! ## Problem shapes (rows of `sil project`)

The explorer's obligations as shapes, so that `sil project` records them with their statuses
in the project database (`silmaril/compiler-explorer.toml`). A row fixes the model (`.open`:
`Silmaril.X86.Open.isa`) and the function `F`. -/

/-- The translation: the machine, stopped at its first return, refines the Core run, from every
System V call with a safe Core run, in every caller continuation. -/
@[problem "silmaril.shapes.compiler_explorer.c.translation"
  (title := "Compiler explorer: the machine code refines the C function's Core run")]
def ExplorerTranslation (I : Model) (F : FnData) : Prop :=
  ∀ k0, (F.compilation I k0).toProblem.Refines

/-- The translation is not vacuous: a related entry with a safe Core run exists. -/
@[problem "silmaril.shapes.compiler_explorer.c.nonvacuous"
  (title := "Compiler explorer: some System V entry and safe Core entry are related")]
def ExplorerNonvacuous (I : Model) (F : FnData) : Prop :=
  (F.compilation I []).toProblem.Inhabited

/-- One edge of the mapping: the segment from point `k` is simulated. -/
@[problem "silmaril.shapes.compiler_explorer.c.edge"
  (title := "Compiler explorer: one segment of the mapping is simulated")]
def ExplorerEdge (I : Model) (F : FnData) (k : Nat) : Prop :=
  ∀ k0, (F.mapping I k0).EdgeValid k

/-- The whole mapping: every segment, at every point number. -/
@[problem "silmaril.shapes.compiler_explorer.c.mapping"
  (title := "Compiler explorer: every segment of the mapping is simulated")]
def ExplorerMapping (I : Model) (F : FnData) : Prop :=
  ∀ k0, (F.mapping I k0).Valid

/-- The mapping refines the relation the location semi-comorphism generates. -/
@[problem "silmaril.shapes.compiler_explorer.c.refines_location"
  (title := "Compiler explorer: the mapping refines the C-object-to-frame-slot relation")]
def ExplorerLocation (I : Model) (F : FnData) : Prop :=
  ∀ k0, (F.mapping I k0).toMapping.RefinesAt F.dwarfRel (fun _ => True)

/-- The function's bytes are the code of its symbol in an object file (the binding of a problem's
Lean function to its target artifact). -/
@[problem "silmaril.shapes.compiler_explorer.c.code"
  (title := "Compiler explorer: the function's bytes are its symbol's code in the object")]
def ExplorerCode {V : Type} (obj : Silmaril.Project.Value V) (name : String) (F : FnData) : Prop :=
  Silmaril.Project.Shapes.SysV.ObjectFn obj name F.code

end Silmaril.Project.CompilesTo

end

silmaril instance silmaril.shapes.compiler_explorer.c.translation.open
    (title := "compiler_explorer.c.translation, on the open machine (Open)") :=
  silmaril.shapes.compiler_explorer.c.translation (I := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.compiler_explorer.c.nonvacuous.open
    (title := "compiler_explorer.c.nonvacuous, on the open machine (Open)") :=
  silmaril.shapes.compiler_explorer.c.nonvacuous (I := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.compiler_explorer.c.edge.open
    (title := "compiler_explorer.c.edge, on the open machine (Open)") :=
  silmaril.shapes.compiler_explorer.c.edge (I := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.compiler_explorer.c.mapping.open
    (title := "compiler_explorer.c.mapping, on the open machine (Open)") :=
  silmaril.shapes.compiler_explorer.c.mapping (I := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.compiler_explorer.c.refines_location.open
    (title := "compiler_explorer.c.refines_location, on the open machine (Open)") :=
  silmaril.shapes.compiler_explorer.c.refines_location (I := Silmaril.X86.Open.isa)
