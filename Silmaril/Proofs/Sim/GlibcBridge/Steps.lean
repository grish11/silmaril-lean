module

public import Silmaril.Proofs.Sim.GlibcBridge.Bytes
public import Silmaril.Sim.GlibcBridge.Ext.Defs

/-!
# The import call in the Wasm small-step semantics

The dispatcher semantics `BRun` treats an import call as a contract answer (`extStore0`). Here
it is the Wasm semantics (`Silmaril.Wasm.Execution.Core.Step`, rule `call_ref-hostfunc-res`) of
the method `extCode0`, with `ext.call` and `nd.undef` host functions of `extHost C mem`, as
`Silmaril.Sim.WasiBridge.G.sys_steps` is for the `syscall` method.

* `ggets_exec`: pushing argument registers; `clobber_steps`: the scratch clobbers.
* **`ext_steps`**: `extCode0` runs from `s` to `extStore0 s f v ws` whenever the contract admits
  the call with result `v` and `nd.undef` answers `ws`.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (exec exec1 Steps.of_eq Step.ctx exec_sound)
open Silmaril.X86 (Reg State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.WasiBridge (Obs)
open Silmaril.Sim.WasiBridge.G (HostFn hostFn_funcs hostCall_steps upd_funcs steps_exec)

variable {P : Profile} {C : ImportC} {mem : Memory}

theorem ggets_exec {H : Type} {s : Store H} {f : Frame} {σ : State} (hE : Enc s f σ)
    (regs : List Reg) (rs : List Val) :
    exec s f rs (regs.map fun r => gget (.reg r)) =
      some (s, f, ((regs.map σ.read).map Val.i64).reverse ++ rs) := by
  induction regs generalizing rs with
  | nil => rfl
  | cons r regs ih =>
    simp only [List.map_cons, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hE.2.1 r, Option.map_some,
      ih, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem updRegs_funcs {H : Type} (s : Store H) (f : Frame) (l : List (Reg × Word)) :
    (updRegs s f l).funcs = s.funcs := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact (ih _).trans (upd_funcs _ _ _ _)

theorem layout_updRegs {H : Type} {s : Store H} {f : Frame} (hl : Layout s f)
    (l : List (Reg × Word)) : Layout (updRegs s f l) f := by
  induction l generalizing s with
  | nil => exact hl
  | cons a l ih => exact ih hl.upd'

/-- The scratch clobbers, `nd.undef` answering `ws`. -/
theorem clobber_steps {s : Store ExtTag} {f : Frame} {ux : FuncIdx}
    (hU : HostFn s f ux 1 .undef) (hl : Layout s f) (L : List Reg) (ws : Reg → Word)
    (rest : List Admin) :
    Steps P (extHost C mem) ⟨s, f, expression (L.flatMap (clobberCode ux)) ++ rest⟩
      ⟨updRegs s f (L.map fun q => (q, ws q)), f, rest⟩ := by
  induction L generalizing s with
  | nil => exact Relation.ReflTransGen.refl
  | cons q L ih =>
    show Steps P (extHost C mem) ⟨s, f, expression ((q :: L).flatMap (clobberCode ux)) ++ rest⟩
      ⟨updRegs s f ((q :: L).map fun q => (q, ws q)), f, rest⟩
    obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hU
    let K : List Admin := expression ([gset (.reg q)] ++ L.flatMap (clobberCode ux)) ++ rest
    have hc : exec s f [] [.intConst .i32 (BitVec.ofNat 32 q.toBitVec.toNat)] =
        some (s, f, [Val.i32 (BitVec.ofNat 32 q.toBitVec.toNat)]) := rfl
    have st1 : Steps P (extHost C mem)
        ⟨s, f, vals [] ++ ([Instr.intConst .i32 (BitVec.ofNat 32 q.toBitVec.toNat)].map .plain ++
          (.plain (.call ux) :: K))⟩
        ⟨s, f, vals [Val.i32 (BitVec.ofNat 32 q.toBitVec.toNat)] ++ (.plain (.call ux) :: K)⟩ :=
      steps_exec hc _
    have st2 : Steps P (extHost C mem)
        ⟨s, f, vals [Val.i32 (BitVec.ofNat 32 q.toBitVec.toNat)] ++ .plain (.call ux) :: K⟩
        ⟨s, f, vals [Val.i64 (ws q)] ++ K⟩ :=
      hostCall_steps (h := ExtTag.undef) h1 h2 h3 (by simp [h4]) h5 ⟨ws q, rfl⟩ K
    have hg : exec s f [Val.i64 (ws q)] [gset (.reg q)] =
        some (upd s f (.reg q) (Val.i64 (ws q)), f, []) := by
      simp [Silmaril.Wasm.Logic.Core.exec_cons, exec1_gset hl]
    have st3 : Steps P (extHost C mem) ⟨s, f, vals [Val.i64 (ws q)] ++ K⟩
        ⟨upd s f (.reg q) (Val.i64 (ws q)), f,
          expression (L.flatMap (clobberCode ux)) ++ rest⟩ := by
      have := steps_exec (P := P) (host := extHost C mem) hg
        (expression (L.flatMap (clobberCode ux)) ++ rest)
      simpa [K, expression, vals] using this
    have st4 := ih (s := upd s f (.reg q) (Val.i64 (ws q)))
      (hostFn_funcs (upd_funcs _ _ _ _) ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩) hl.upd'
    refine Relation.ReflTransGen.trans ?_ (st1.trans (st2.trans (st3.trans st4)))
    exact Steps.of_eq (by simp [K, clobberCode, expression, vals])

/-- **The import call's method in the Wasm semantics**: when the contract admits the call of
the argument registers with result `v` and `nd.undef` answers `ws`, `extCode0` runs to
`extStore0 s f v ws`. -/
theorem ext_steps {s : Store ExtTag} {f : Frame} {ex ux : FuncIdx} {regs : List Reg}
    (hX : HostFn s f ex regs.length .ext) (hU : HostFn s f ux 1 .undef) {σ : State}
    (hE : Enc s f σ) {obs : List Obs} {v : Word} (hc : C mem (regs.map σ.read) obs (some v))
    (ws : Reg → Word) (rest : List Admin) :
    Steps P (extHost C mem) ⟨s, f, expression (extCode0 ex ux regs) ++ rest⟩
      ⟨extStore0 s f v ws, f, rest⟩ := by
  have hl : Layout s f := hE.1
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hX
  let s₁ := upd s f (.reg .rax) (Val.i64 v)
  let K₂ : List Admin := expression (scratch.flatMap (clobberCode ux)) ++ rest
  let K₁ : List Admin := expression [gset (.reg .rax)] ++ K₂
  let K₀ : List Admin := .plain (.call ex) :: K₁
  have st1 : Steps P (extHost C mem) ⟨s, f, expression (regs.map fun r => gget (.reg r)) ++ K₀⟩
      ⟨s, f, vals ((regs.map σ.read).map Val.i64) ++ K₀⟩ := by
    have := steps_exec (P := P) (host := extHost C mem) (ggets_exec hE regs []) K₀
    simpa [vals, expression] using this
  have st2 : Steps P (extHost C mem) ⟨s, f, vals ((regs.map σ.read).map Val.i64) ++ K₀⟩
      ⟨s, f, vals [Val.i64 v] ++ K₁⟩ :=
    hostCall_steps (h := ExtTag.ext) h1 h2 h3 (by simp [h4]) h5 ⟨_, obs, v, rfl, hc, rfl⟩ K₁
  have hg : exec s f [Val.i64 v] [gset (.reg .rax)] = some (s₁, f, []) := by
    simp [s₁, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gset hl]
  have st3 : Steps P (extHost C mem) ⟨s, f, vals [Val.i64 v] ++ K₁⟩ ⟨s₁, f, K₂⟩ := by
    have := steps_exec (P := P) (host := extHost C mem) hg K₂
    simpa [K₁, vals] using this
  have hU₁ : HostFn s₁ f ux 1 .undef := hostFn_funcs (upd_funcs _ _ _ _) hU
  have st4 := clobber_steps (P := P) (C := C) (mem := mem) hU₁ hl.upd' scratch ws rest
  refine Relation.ReflTransGen.trans ?_ (st1.trans (st2.trans (st3.trans st4)))
  exact Steps.of_eq (by simp [extCode0, expression, K₀, K₁, K₂])

/-- **The dispatcher's `ext` step is a Wasm run**: the import call's method followed by the
driver's `ret` (GM's method `rc`, as `BRun.ext` executes it) runs from `s` to the store `BRun`
continues from. -/
theorem ext_ret_steps {s s' : Store ExtTag} {f : Frame} {ex ux : FuncIdx} {regs : List Reg}
    (hX : HostFn s f ex regs.length .ext) (hU : HostFn s f ux 1 .undef) {σ : State}
    (hE : Enc s f σ) {obs : List Obs} {v : Word} (hc : C mem (regs.map σ.read) obs (some v))
    (ws : Reg → Word) {rc : List Instr} (he : exec (extStore0 s f v ws) f [] rc = some (s', f, []))
    (rest : List Admin) :
    Steps P (extHost C mem) ⟨s, f, expression (extCode0 ex ux regs ++ rc) ++ rest⟩
      ⟨s', f, rest⟩ := by
  have h₁ := ext_steps (P := P) hX hU hE hc ws (expression rc ++ rest)
  have h₂ := steps_exec (P := P) (host := extHost C mem) he rest
  simp only [List.reverse_nil, vals, List.map_nil, List.nil_append] at h₂
  simpa [expression, List.append_assoc] using h₁.trans h₂

end Silmaril.Sim.GlibcBridge
