module

public import Silmaril.Elf.Region.Calls.Semantic.Defs
public import Silmaril.Semantics.Function.Semantic.Thms
import Silmaril.Proofs.Elf.Region.CallSemantics

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function
open Silmaril.X86 (Byte MState Word State)

theorem ext_covers {plan : Plan} {owner : Owner} {source : signature.Context} {inventory : Inventory}
    (exit : Word) (sites : SiteCoverage plan owner source inventory) :
    CallGraphProblem ((extModel plan exit owner).actualCalls source) (analysis inventory) :=
  Proofs.ext_covers exit sites

theorem restrict_sites {plan : Plan} {owner refined : Owner} {source : signature.Context} {inventory : Inventory}
    (sites : SiteCoverage plan owner source inventory)
    (restrict : ∀ caller state, refined source caller state → owner source caller state) :
    SiteCoverage plan refined source inventory :=
  fun caller state site callee owns observed => sites caller state site callee (restrict caller state owns) observed

theorem call_retirement {exit : Word} {pre : MState} {code : List Byte} {displacement : BitVec 32}
    {core : State} {after : Silmaril.Process.Memory}
    (fetched : pre.memory.fetchBytes pre.core.rip.toNat 5 = some code)
    (decoded : Silmaril.X86.Ext.decode code = some (.call displacement, 5))
    (push : Silmaril.X86.pushWord pre.core pre.memory (pre.core.rip + 5#64) = some (core, after)) :
    (Silmaril.Machine.Region.X86.system exit).step pre []
      ⟨{core with rip := pre.core.rip + 5#64 + displacement.signExtend 64}, after⟩ :=
  Proofs.call_retirement fetched decoded push

end Silmaril.Elf.Region.Calls
