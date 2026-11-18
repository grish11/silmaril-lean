module

public import Silmaril.Proofs.Sim.SysV.Edge
public import Silmaril.Sim.X86.Max.Thms

/-!
# A second function through the generic edge: `add2`

`mov rax, rdi; add rax, rsi; ret` (`48 89 f8 48 01 f0 c3`). The only proof obligations are the
body's Wasm problem (`add2_wasm`, by `g_vc`) and the two glue facts, discharged by
`preGlue_true` and `postGlue_of_frame` + `simp` (`add2_xgoal`); retirement is automatic.
`add2_sysv`: the x86 System V statement on the bytes, any number of stack arguments.
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg State MState Word)
open Silmaril.Sim.X86.G

/-- The body of `add2`, decoded. -/
def add2Prog : XProg := [(.mov .q (.reg .rax) .rdi, 3), (.alu .q .add (.reg .rax) .rsi, 3)]

/-- The bytes of `add2`, `ret` last. -/
def add2Bytes : List (List (BitVec 8)) := [[0x48, 0x89, 0xf8], [0x48, 0x01, 0xf0], [0xc3]]

/-- The generated Wasm code of the body. -/
def add2Code : List Instr :=
  [gget (.reg .rdi), gset (.reg .rax)] ++ nextCode 3 ++ aluCode .add .rax .rsi ++ nextCode 3

/-- Body spec: `rax = rdi + rsi`, every other register unchanged. -/
def Add2Post (R R' : Reg → Word) : Prop := R' .rax = R .rdi + R .rsi ∧ ∀ r, r ≠ .rax → R' r = R r

theorem add2_emit : emitProg add2Prog = some add2Code := rfl

theorem add2_wasm {H : Type} {P : Profile} {host : HostSemantics H} :
    WProblem (H := H) P host add2Code (fun _ => True) Add2Post := by
  intro s f R ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ _
  apply hwp_of_wpc (fun _ _ _ _ => True)
  g_vc [add2Code, hl, hr, hw, hc, hz, hs, ho, List.append_assoc]
  refine ⟨trivial, fun R' h => ⟨?_, fun r hr => ?_⟩⟩
  · have h' := h .rax
    simp only [ite_true, Option.some.injEq, val_i64_inj] at h'
    exact h'.symm
  · have h' := h r
    simp only [hr, ite_false, Option.some.injEq, val_i64_inj] at h'
    exact h'.symm

/-- The call-level spec: `rax` is the sum of the first two arguments. -/
def Add2CallPost (d : SysVCall) (r : Word) : Prop := r = d.regArgs.getD 0 0 + d.regArgs.getD 1 0

/-- **The x86 problem of `add2` through the wrapper**: Wasm problem + glue, nothing else. -/
theorem add2_xgoal (n : Nat) : XGoal add2Prog n (fun d => d.intArgs.length ≤ 6) Add2CallPost :=
  xgoal_of_body (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    add2_emit n add2_wasm (preGlue_true _)
    (postGlue_of_frame (Q := fun R v => v = R .rdi + R .rsi) (fun _ _ h => h)
      (fun d σ v hk hv => by
        obtain ⟨h0, h1, -⟩ := entryCore_read d σ hk
        simp only [Add2CallPost, hv, h0, h1]))

theorem add2Bytes_decode : ∀ (k : Nat) (_h₁ : k < (add2Prog ++ [(Silmaril.X86.Ext.Instr.ret, 1)]).length)
    (h₂ : k < add2Bytes.length),
    Silmaril.X86.Ext.decode add2Bytes[k] = some (add2Prog ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k] ∧
      (add2Prog ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k].2 = add2Bytes[k].length := by
  decide

/-- **`add2` on the bytes, through the System V convention**, for any caller whose modelled
flags are defined. -/
theorem add2_sysv (d : SysVCall) (hd : d.Valid) (m e : MState) (hs : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8)
    (hb : BytesAt e.memory d.target add2Bytes) (hf : FlagsDef m.core) :
    Silmaril.X86.FnContract.AbiEntry e.core e.memory ∧ ∃ final : MState,
      Silmaril.X86.Ext.Returns SENTINEL e final ∧
      Silmaril.X86.FnContract.AbiReturn e.core e.memory final.core ∧
      Add2CallPost d (final.core.read .rax) :=
  XGoal.of_flags add2_emit (add2_xgoal _) d m e hd rfl hd.1 hs hr
    (codeAt_of_bytesAt rfl add2Bytes_decode hb) hf

end Silmaril.Sim.SysV
