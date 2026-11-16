module

public import Silmaril.Proofs.Sim.X86.Max.X86
public import Silmaril.X86.Open9.Thms

/-!
# `max` as a System V function contract on `Open9.isa`

`maxSpec`: entry = the bytes `maxBytes` at RIP; footprint = nothing; post = `rax` is the signed
maximum of `rdi` and `rsi`. **`maxContract : FnContract Open9.isa`** (total correctness, the
recommended contract form of `docs/x86-models.md`), from `max_returns` (whose functional part is
the Wasm solution, transported by `Silmaril.Sim.X86.G.xproblem_of_wproblem`), `Open.returns_open_ext` and
`Open9.reaches_of_open`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Max

open Silmaril.X86 (Reg State MState Word Byte sysv64)
open Silmaril.X86
open Silmaril.Sim.X86.G

/-- **`max` meets its System V contract on `Open9.isa`.** -/
theorem maxSpec_total : maxSpec.Total Open9.isa := by
  intro s _ habi hentry
  obtain ⟨final, hret, hrip, hrax, hframe, hrsp, hmem⟩ :=
    max_returns s (Silmaril.X86.FnContract.retOf s.core s.memory) hentry habi.returnAddress
      (Silmaril.X86.wordOfBytes?_encodeWords _)
  obtain ⟨hreach, -⟩ := Open.returns_open_ext hret
  refine ⟨final, Open9.reaches_of_open hreach, rfl, ⟨hrip, hrsp, fun r hr => hframe r ?_ ?_⟩,
    ?_, hrax⟩
  · rintro rfl; simp [sysv64] at hr
  · rintro rfl; exact Silmaril.X86.sysv64_rsp_not_calleeSaved hr
  · show s.memory.WritesWithin final.memory _
    rw [hmem]
    exact Silmaril.Process.Memory.WritesWithin.refl _ _

/-- **`max` as a System V function contract** on `Open9.isa`. -/
def maxContract : FnContract Open9.isa := ⟨maxSpec, maxSpec_total⟩

end Silmaril.Sim.X86.Max
