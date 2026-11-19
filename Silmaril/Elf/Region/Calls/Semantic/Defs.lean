module

public import Silmaril.Elf.Region.Calls.Defs
public import Silmaril.Machine.Region.X86.Defs
public import Silmaril.Semantics.Function.Semantic.Defs

/-! # An operational interpretation of the direct Ext subset

Observation decodes executable loaded bytes at the pre-state PC. The actual
step must retire, including the stack write. A foreign edge means transfer to
a declared stub, not that the loader will link it or the external body will
return. Indirect and tail semantics are not supplied by this profile.
-/

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function
open Silmaril.X86 (MState Word)
open Silmaril.X86.Decompile (Decoded)

abbrev Owner := signature.Context → Nat → MState → Prop

def observe (plan : Plan) (state : MState) : Option (Nat × Node signature) := do
  let site := state.core.rip.toNat
  let bytes ← state.memory.fetchBytes site 5
  let some (.call displacement, 5) := Silmaril.X86.Ext.decode bytes | none
  let instr : Decoded := ⟨site, .call displacement, 5⟩
  let callee ← resolve plan (instr.relTarget (displacement.signExtend 64))
  pure (site, callee)

def nodeAddress : Node signature → Nat
  | .localFn addr => addr
  | .foreign stub => stub.address

def extModel (plan : Plan) (exit : Word) (owner : Owner) : Machine signature where
  State := MState
  Label := Nat
  Event := Empty
  Stop := Silmaril.X86.Ext.Outcome
  system _ := Silmaril.Machine.Region.X86.system exit
  owner := owner
  event _ pre _ _ edge := observe plan pre = some (edge.origin.site, edge.callee) ∧
    edge.origin.transfer = .invoke ∧ edge.dispatch = .direct
  invocation _ _ callee _ post := post.core.rip.toNat = nodeAddress callee
  tailTransfer _ _ _ _ _ := False
  returned _ _ := Silmaril.X86.Ext.Returns exit

/-- Source/placement agreement at admitted call sites is an independent
obligation. In particular a parsed ELF header does not imply this relation. -/
def SiteCoverage (plan : Plan) (owner : Owner) (source : signature.Context)
    (inventory : Inventory) : Prop :=
  ∀ caller pre site callee, owner source caller pre → observe plan pre = some (site, callee) →
    (analysis inventory).direct ⟨caller, site, .invoke⟩ callee

end Silmaril.Elf.Region.Calls
