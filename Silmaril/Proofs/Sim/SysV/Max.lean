module

public import Silmaril.Proofs.Sim.SysV.Decomp
public import Silmaril.Sim.X86.Max.Thms

/-!
# `max` called through the System V wrapper, end to end

* `MaxCallPost d r`: `r` is the signed maximum of the first two register arguments.
* **`max_wgoal`**: the wrapper's Wasm problem for `max` (`WGoal`), from the G
  solution of the body (`Silmaril.Sim.X86.Max.wasm_solution`, solved with `wpc`) by the
  decomposition `wgoal_of_body`. No x86 reasoning beyond retirement of the body.
* **`max_xgoal`**: the x86 problem, by `xgoal_of_wgoal`.
* **`max_sysv`**: on the `Silmaril.X86.Ext` machine, for every caller state and descriptor
  (any number of stack arguments, which `max` ignores), if the entry state can be set up, the sentinel slot is readable and
  the bytes of `max` (`maxBytes`) are at the target, the entry state meets `AbiEntry` and
  `max` returns to the sentinel (first return) meeting `AbiReturn` with `rax` the signed maximum
  of the first two arguments.
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg State MState Word)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.X86.Max
open Silmaril.X86.FnContract (AbiEntry AbiReturn)

theorem entryCore_args (d : SysVCall) (σ : State) (hk : d.intArgs.length ≤ 6) :
    (entryCore d σ).read .rdi = d.regArgs.getD 0 0 ∧ (entryCore d σ).read .rsi = d.regArgs.getD 1 0 := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, ha⟩ := list6 d.regArgs (regArgs_length' d hk)
  simp only [entryCore, ha, setArgs, Silmaril.X86.sysv64]
  constructor <;> simp [State.read, State.write, Silmaril.Machine.RegisterFile.write]

/-- **The wrapper's Wasm problem for `max`**, solved. -/
theorem max_wgoal {H : Type} {P : Profile} {host : HostSemantics H} {n : Nat} :
    WGoal P host maxCode n (fun d => d.intArgs.length ≤ 6) MaxCallPost := by
  refine wgoal_of_body (p := maxProg) rfl wasm_solution (fun _ _ _ => trivial) (fun d σ R' hk hp => ?_)
  obtain ⟨hmax, hfr⟩ := hp
  obtain ⟨h0, h1⟩ := entryCore_args d σ hk
  refine ⟨⟨hfr _ (by decide), hfr _ (by decide), hfr _ (by decide), hfr _ (by decide),
    hfr _ (by decide), hfr _ (by decide), hfr _ (by decide)⟩, ?_⟩
  rw [MaxCallPost, hmax, h0, h1]

/-- **The x86 problem for `max` through the wrapper**, solved by reduction. -/
theorem max_xgoal (n : Nat) : XGoal maxProg n (fun d => d.intArgs.length ≤ 6) MaxCallPost :=
  xgoal_of_wgoal (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False) rfl max_wgoal

/-- **`max` on the bytes, called by the System V convention.** -/
theorem max_sysv (d : SysVCall) (hd : d.Valid) (m e : MState)
    (hsetup : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8)
    (hb : BytesAt e.memory d.target maxBytes) :
    AbiEntry e.core e.memory ∧ ∃ final : MState, Silmaril.X86.Ext.Returns SENTINEL e final ∧
      AbiReturn e.core e.memory final.core ∧ MaxCallPost d (final.core.read .rax) := by
  have hcode := codeAt_of_bytesAt (p := maxProg ++ [(.ret, 1)]) rfl maxBytes_decode hb
  obtain ⟨σ', h⟩ := maxProg_runs e.core e.memory
  exact max_xgoal _ d m e hd rfl hd.1 hsetup hr hcode ⟨σ', e.memory, h⟩

end Silmaril.Sim.SysV
