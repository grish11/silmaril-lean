module

public import Silmaril.Elf.Region.Calls.Semantic.Defs
public import Silmaril.Semantics.Function.Semantic.Thms

public section
namespace Silmaril.Elf.Region.Calls.Proofs
open Silmaril.Semantics.Function
open Silmaril.X86 (Byte MState Word State)

theorem ext_covers {plan : Plan} {owner : Owner} {source : signature.Context} {inventory : Inventory}
    (exit : Word) (sites : SiteCoverage plan owner source inventory) :
    CallGraphProblem ((extModel plan exit owner).actualCalls source) (analysis inventory) := by
  rintro ⟨⟨caller, site, transfer⟩, tag, callee⟩ ⟨pre, _, owns, _, _, event, _⟩
  change observe plan pre = some (site, callee) ∧ transfer = .invoke ∧ tag = .direct at event
  obtain ⟨observed, rfl, rfl⟩ := event
  exact sites caller pre site callee owns observed

theorem call_retirement {exit : Word} {pre : MState} {code : List Byte} {displacement : BitVec 32}
    {core : State} {after : Silmaril.Process.Memory}
    (fetched : pre.memory.fetchBytes pre.core.rip.toNat 5 = some code)
    (decoded : Silmaril.X86.Ext.decode code = some (.call displacement, 5))
    (push : Silmaril.X86.pushWord pre.core pre.memory (pre.core.rip + 5#64) = some (core, after)) :
    (Silmaril.Machine.Region.X86.system exit).step pre []
      ⟨{core with rip := pre.core.rip + 5#64 + displacement.signExtend 64}, after⟩ := by
  refine ⟨rfl, ?_⟩
  rw [Silmaril.X86.Ext.step_of_fetch fetched decoded, Silmaril.X86.Decompile.exec_call]
  have length : (Silmaril.X86.Ext.Instr.call displacement).length = 5 := rfl
  simp [length, push]

end Silmaril.Elf.Region.Calls.Proofs
