module

public import Silmaril.Proofs.Sim.SysV.Decomp

/-!
# The wrapper as reduction edges, for any program of the G fragment

For every straight-line x86 body `p` that the G simulator translates
(`emitProg p = some code`) and every number `n` of stack arguments:

* **`xgoal_of_body`**: the x86 System V problem `XGoal p n Pre Post` follows from the body's
  Wasm problem `WProblem P host code BPre BPost` and two register side conditions (`PreGlue`,
  `PostGlue`); retirement is automatic (`runExt_progress`). The composite of `wgoal_of_body`
  and `xgoal_of_wgoal`. `XGoal.of_flags`: `XGoal`'s retirement hypothesis replaced by defined flags.
* Glue by `simp`: `preGlue_true`, `postGlue_of_frame` (a body spec of the form "rax meets `Q`,
  every other register unchanged"), `entryCore_rdi`…`entryCore_r9` (`simp` lemmas).
* **`decomp`**: the same as a `Silmaril.Sim.Reduce.Decomp` (goal + pieces + composition theorem),
  the shape of an edge of a problem DAG (`silmaril.wasm-sim.dag.v0`: `goal`, `pieces`, `theorem`).
  Pieces: `wasm/body` (a Wasm problem), `glue/pre`, `glue/post` (register facts about
  `entryCore`, no Wasm, no memory).
* `wrapperReduction`: the two-step chain `WProblem → WGoal → XGoal` as one
  `Silmaril.Sim.Reduce.Reduction` (`Reduction.trans` of `reduction` with the decomposition).
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg State Word)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G

variable {H : Type}

/-- **Any G-fragment function through the wrapper**: the body's Wasm problem and the glue
solve the x86 System V problem, for any number of stack arguments. -/
theorem xgoal_of_body {P : Profile} {host : HostSemantics H} {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) (n : Nat) {Pre : SysVCall → Prop} {Post : SysVCall → Word → Prop}
    {BPre : (Reg → Word) → Prop} {BPost : (Reg → Word) → (Reg → Word) → Prop}
    (hW : WProblem P host code BPre BPost) (hpre : PreGlue Pre BPre)
    (hpost : PostGlue Pre BPost Post) : XGoal p n Pre Post :=
  xgoal_of_wgoal hc (wgoal_of_body hc hW hpre hpost)

/-- **The DAG edge**: `XGoal` decomposed into one Wasm problem and three side conditions. -/
def decomp (P : Profile) (host : HostSemantics H) {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) (n : Nat) (Pre : SysVCall → Prop) (Post : SysVCall → Word → Prop)
    (BPre : (Reg → Word) → Prop) (BPost : (Reg → Word) → (Reg → Word) → Prop) :
    Silmaril.Sim.Reduce.Decomp where
  goal := XGoal p n Pre Post
  pieces := [WProblem P host code BPre BPost, PreGlue Pre BPre, PostGlue Pre BPost Post]
  compose h := xgoal_of_body hc n (h (WProblem P host code BPre BPost) (by simp))
    (h (PreGlue Pre BPre) (by simp)) (h (PostGlue Pre BPost Post) (by simp))

/-- The chain `WProblem (body) → XGoal` as one reduction, given the side conditions. -/
def wrapperReduction (P : Profile) (host : HostSemantics H) {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) (n : Nat) {Pre : SysVCall → Prop} {Post : SysVCall → Word → Prop}
    {BPre : (Reg → Word) → Prop} {BPost : (Reg → Word) → (Reg → Word) → Prop}
    (hpre : PreGlue Pre BPre) (hpost : PostGlue Pre BPost Post) :
    Silmaril.Sim.Reduce.Reduction where
  src := XGoal p n Pre Post
  tgt := WProblem P host code BPre BPost
  sound hW := xgoal_of_body hc n hW hpre hpost

/-! ## Discharging the side conditions -/

/-- `XGoal`'s retirement hypothesis is automatic when the caller's modelled flags are defined. -/
theorem XGoal.of_flags {p : XProg} {code : List Instr} (hc : emitProg p = some code) {n : Nat}
    {Pre : SysVCall → Prop} {Post : SysVCall → Word → Prop} (h : XGoal p n Pre Post)
    (d : SysVCall) (m e : Silmaril.X86.MState) (hd : d.Valid) (hn : d.stackArgs.length = n)
    (hp : Pre d) (hs : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp n (m.core.read .rsp)).toNat 8)
    (hcode : CodeAt e.memory d.target (p ++ [(.ret, 1)])) (hf : FlagsDef m.core) :
    Silmaril.Machine.X86.FnContract.AbiEntry e.core e.memory ∧
      ∃ final : Silmaril.X86.MState, Silmaril.X86.Ext.Returns SENTINEL e final ∧
        Silmaril.Machine.X86.FnContract.AbiReturn e.core e.memory final.core ∧
        Post d (final.core.read .rax) := by
  have hf' : FlagsDef e.core := by rw [setup_core hs]; exact flagsDef_entryCore hf
  obtain ⟨σ', hx⟩ := runExt_progress hc e.core hf' e.memory
  exact h d m e hd hn hp hs hr hcode ⟨σ', e.memory, hx⟩

theorem preGlue_true (Pre : SysVCall → Prop) : PreGlue Pre fun _ => True := fun _ _ _ => trivial

theorem entryCore_read (d : SysVCall) (σ : State) (hk : d.intArgs.length ≤ 6) :
    (entryCore d σ).read .rdi = d.regArgs.getD 0 0 ∧ (entryCore d σ).read .rsi = d.regArgs.getD 1 0 ∧
    (entryCore d σ).read .rdx = d.regArgs.getD 2 0 ∧ (entryCore d σ).read .rcx = d.regArgs.getD 3 0 ∧
    (entryCore d σ).read .r8 = d.regArgs.getD 4 0 ∧ (entryCore d σ).read .r9 = d.regArgs.getD 5 0 := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, ha⟩ := list6 d.regArgs (regArgs_length' d hk)
  simp only [entryCore, ha, setArgs, Silmaril.X86.sysv64]
  simp [State.read, State.write, Silmaril.Machine.RegisterFile.write]

/-- A body spec "`rax` meets `Q`, every other register unchanged" gives `PostGlue`. -/
theorem postGlue_of_frame {Pre : SysVCall → Prop} {BPost : (Reg → Word) → (Reg → Word) → Prop}
    {Post : SysVCall → Word → Prop} {Q : (Reg → Word) → Word → Prop}
    (hb : ∀ R R', BPost R R' → Q R (R' .rax) ∧ ∀ r, r ≠ .rax → R' r = R r)
    (hq : ∀ d σ v, Pre d → Q (entryCore d σ).read v → Post d v) : PostGlue Pre BPost Post := by
  intro d σ R' hp h
  obtain ⟨hQ, hfr⟩ := hb _ _ h
  exact ⟨⟨hfr _ (by decide), hfr _ (by decide), hfr _ (by decide), hfr _ (by decide),
    hfr _ (by decide), hfr _ (by decide), hfr _ (by decide)⟩, hq d σ _ hp hQ⟩

end Silmaril.Sim.SysV
