module

public import Silmaril.Proofs.Sim.WasiBridge.G.Wasm

/-!
# The `syscall` method in the Wasm small-step semantics

The interaction semantics `WRun` treats the `syscall` method's two import calls as environment
answers. Here they are the Wasm semantics (`Silmaril.Wasm.Execution.Core.Step`, rule
`call_ref-hostfunc-res`) of the method's code, for a store whose function indices `sx`, `ux`
resolve to host functions (`HostFuncs`) of the host relation `s1Host mem`: `sys.syscall` answers
as the `sys2wasi` adapter does for `S1` (`S1Ans`), `nd.undef` answers anything.

* `hostCall_steps`: a call of a host function that returns `v` without touching the store.
* `exec_funcs`: straight-line code does not change the function instances.
* **`sys_steps`**: the `syscall` method's code runs from `s` to `sysStore s f r v w` exactly when
  the environment answers `v` and `w`.
* **`wrun_steps`**: every complete interaction run is a Wasm run of the simulator code.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (exec exec1 Steps.of_eq Step.ctx exec_sound)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G

/-- The host functions of the stack. -/
inductive SysTag where
  | sys | undef

/-- **The environment as a Wasm host relation**: `sys.syscall` answers by `S1Ans mem` (the
`sys2wasi` adapter's `write` answers; `exit` never returns), `nd.undef` answers anything; neither
changes the store. -/
def s1Host (mem : Memory) : HostSemantics SysTag := fun h s vs o =>
  match h with
  | .sys => ∃ args v, vs = args.map Val.i64 ∧ S1Ans mem args v ∧ o = .returned s (.values [Val.i64 v])
  | .undef => ∃ w : Word, o = .returned s (.values [Val.i64 w])

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem hostCall_steps {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {vs : List Val} {v : Val}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fi.code = .host h)
    (hh : host h s vs (.returned s (.values [v]))) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ .plain (.call x) :: rest⟩ ⟨s, f, vals [v] ++ rest⟩ := by
  have h₁ := Step.ctx (P := P) (host := host) vs rest (Step.call (s := s) (f := f) hx hf)
  have h₂ := Step.ctx (P := P) (host := host) [] rest
    (Step.callRefHost (c := .callRefType fi.type) (f := f) trivial hf he hn hcode hh)
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc, List.cons_append,
    Result.toAdmin] at h₁ h₂ ⊢
  exact Relation.ReflTransGen.head h₁ (Relation.ReflTransGen.single h₂)

/-- A host function of type `[i64]^k → [i64]` (`k` parameters) at index `x`. -/
def HostFn (s : Store H) (f : Frame) (x : FuncIdx) (k : Nat) (h : H) : Prop :=
  ∃ a fi ps rs, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
    Expand fi.type (.func ps rs) ∧ ps.length = k ∧ fi.code = .host h

theorem hostFn_funcs {s s' : Store H} {f : Frame} {x : FuncIdx} {k : Nat} {h : H}
    (hs : s'.funcs = s.funcs) (hf : HostFn s f x k h) : HostFn s' f x k h := by
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hf
  exact ⟨a, fi, ps, rs, h1, hs ▸ h2, h3, h4, h5⟩

theorem upd_funcs (s : Store H) (f : Frame) (l : Loc) (v : Val) : (upd s f l v).funcs = s.funcs := by
  unfold upd; split <;> rfl

theorem steps_exec {s s' : Store H} {f : Frame} {rs rs' : List Val} {is : List Instr}
    (h : exec s f rs is = some (s', f, rs')) (rest : List Admin) :
    Steps P host ⟨s, f, vals rs.reverse ++ (is.map .plain ++ rest)⟩ ⟨s', f, vals rs'.reverse ++ rest⟩ := by
  have := exec_sound (P := P) (host := host) rest h
  simpa only [expression, List.append_assoc] using this

/-- An `i32.const` of a literal. -/
private theorem exec1_i32 (s : Store H) (f : Frame) (rs : List Val) (n : Nat) :
    exec1 s f rs (.intConst .i32 (BitVec.ofNat IntType.i32.width n)) =
      some (s, f, Val.i32 (BitVec.ofNat 32 n) :: rs) := rfl

/-- **The `syscall` method's code, in the Wasm semantics**, with the environment answering `v`
(`sys.syscall`) and `w` (`nd.undef`). -/
theorem sys_steps {mem : Memory} {s : Store SysTag} {f : Frame} {sx ux : FuncIdx}
    (hS : HostFn s f sx 7 .sys) (hU : HostFn s f ux 1 .undef) {σ : State} (hE : Enc s f σ) {v w : Word}
    (hans : S1Ans mem (sysRegs.map σ.read) v) (rest : List Admin) :
    Steps P (s1Host mem) ⟨s, f, expression (sysCode sx ux) ++ rest⟩
      ⟨sysStore s f σ.rip v w, f, rest⟩ := by
  have hl : Layout s f := hE.1
  have hr : ∀ r : Reg, gval s f (.reg r) = some (Val.i64 (σ.read r)) := hE.2.1
  have hrip : gval s f .rip = some (Val.i64 σ.rip) := hE.2.2.1
  -- the seven argument pushes
  have hA : exec s f [] (sysRegs.map fun r => gget (.reg r)) =
      some (s, f, ((sysRegs.map σ.read).map Val.i64).reverse) := by
    simp [sysRegs, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hr]
  -- after sys.syscall: rax := v, rcx := rip + 2, push 11
  let s₂ := upd (upd s f (.reg .rax) (Val.i64 v)) f (.reg .rcx) (Val.i64 (σ.rip + 2))
  have hC : exec s f [Val.i64 v] [gset (.reg .rax), gget .rip, c64 2, b64op .add, gset (.reg .rcx),
      .intConst .i32 11] = some (s₂, f, [Val.i32 11]) := by
    simp [Silmaril.Wasm.Logic.Core.exec_cons, exec1_gset hl, exec1_gget, gval_upd hl, hrip, exec1_c64,
      exec1_add, exec1_gset hl.upd', s₂, exec1_i32]
  -- after nd.undef: r11 := w, rip += 2
  have hE₂ : exec s₂ f [Val.i64 w] ([gset (.reg .r11)] ++ nextCode 2) =
      some (sysStore s f σ.rip v w, f, []) := by
    simp [s₂, nextCode, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gset hl.upd'.upd', exec1_gget, gval_upd hl,
      gval_upd hl.upd', gval_upd hl.upd'.upd', hrip, exec1_c64, exec1_add, exec1_gset hl.upd'.upd'.upd',
      sysStore]
  have hfu : s₂.funcs = s.funcs := by simp [s₂, upd_funcs]
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨a', fi', ps', rs', h1', h2', h3', h4', h5'⟩ := hostFn_funcs hfu hU
  have hlen : ((sysRegs.map σ.read).map Val.i64).length = ps.length := by simp [sysRegs, h4]
  -- the code after each of the five pieces
  let K₃ : List Admin := ([gset (.reg .r11)] ++ nextCode 2).map .plain ++ rest
  let K₂ : List Admin := .plain (.call ux) :: K₃
  let K₁ : List Admin := [gset (.reg .rax), gget .rip, c64 2, b64op .add, gset (.reg .rcx),
    .intConst .i32 11].map .plain ++ K₂
  let K₀ : List Admin := .plain (.call sx) :: K₁
  have step1 : Steps P (s1Host mem) ⟨s, f, (sysRegs.map fun r => gget (.reg r)).map .plain ++ K₀⟩
      ⟨s, f, vals ((sysRegs.map σ.read).map Val.i64) ++ K₀⟩ := by
    simpa only [List.reverse_nil, List.reverse_reverse, vals, List.map_nil, List.nil_append] using
      steps_exec (P := P) (host := s1Host mem) hA K₀
  have step2 : Steps P (s1Host mem) ⟨s, f, vals ((sysRegs.map σ.read).map Val.i64) ++ K₀⟩
      ⟨s, f, vals [Val.i64 v] ++ K₁⟩ :=
    hostCall_steps h1 h2 h3 hlen h5 ⟨_, v, rfl, hans, rfl⟩ K₁
  have step3 : Steps P (s1Host mem) ⟨s, f, vals [Val.i64 v] ++ K₁⟩ ⟨s₂, f, vals [Val.i32 11] ++ K₂⟩ :=
    steps_exec hC K₂
  have step4 : Steps P (s1Host mem) ⟨s₂, f, vals [Val.i32 11] ++ K₂⟩ ⟨s₂, f, vals [Val.i64 w] ++ K₃⟩ :=
    hostCall_steps (h := SysTag.undef) h1' h2' h3' (by simp [h4']) h5' ⟨w, rfl⟩ K₃
  have step5 : Steps P (s1Host mem) ⟨s₂, f, vals [Val.i64 w] ++ K₃⟩ ⟨sysStore s f σ.rip v w, f, rest⟩ :=
    steps_exec hE₂ rest
  refine Relation.ReflTransGen.trans ?_ (step1.trans (step2.trans (step3.trans (step4.trans step5))))
  exact Steps.of_eq (by simp [sysCode, expression, K₀, K₁, K₂, K₃])

theorem sysStore_funcs (s : Store H) (f : Frame) (r v w : Word) : (sysStore s f r v w).funcs = s.funcs := by
  simp [sysStore, upd_funcs]

theorem flagsDef_sysCore {σ : State} (h : FlagsDef σ) (v w : Word) : FlagsDef (sysCore σ v w) := h

/-- **Interaction runs are Wasm runs**: from a store encoding a core with defined modelled
flags, whose `sx`/`ux` are the environment's host functions, every interaction run of the
simulator code of `items` is a run of the Wasm small-step semantics (with `s1Host`) of its code,
up to the code of the items not executed. -/
theorem wrun_steps {mem : Memory} {f : Frame} {sx ux : FuncIdx} {items rest : List Item}
    {evs : List HostEv} {s : Store SysTag} (hw : WRun (S1Ans mem) s f items evs rest) :
    ∀ {σ : State} {code codeR : List Instr}, Enc s f σ → FlagsDef σ → HostFn s f sx 7 .sys →
      HostFn s f ux 1 .undef → emitItems sx ux items = some code → emitItems sx ux rest = some codeR →
      ∃ s', Steps P (s1Host mem) ⟨s, f, expression code⟩ ⟨s', f, expression codeR⟩ := by
  intro σ code codeR hE hσ hS hU hcode hr
  induction hw generalizing σ code codeR with
  | stop s f p =>
    have hcc : codeR = code := Option.some.inj (hr.symm.trans hcode)
    exact ⟨s, by rw [hcc]⟩
  | @ins s s' f i n c p rest evs hc he _ ih =>
    show ∃ s₃, Steps P (s1Host mem) ⟨s, f, expression code⟩ ⟨s₃, f, expression codeR⟩
    obtain ⟨c', hc', cs, hcs, hcode'⟩ : ∃ c', emit i n = some c' ∧
        ∃ cs, emitItems sx ux p = some cs ∧ c' ++ cs = code := by
      simpa only [emitItems, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] using hcode
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨σ', hx, hσ'⟩ := step_progress hcore σ hσ ⟨[], ∅⟩ n
    obtain ⟨-, s'', he', hE', hF⟩ := emit_sound hc hE hx
    have hs'' : s'' = s' := (Prod.mk.inj (Option.some.inj (he'.symm.trans he))).1
    have hE₁ : Enc s' f σ' := hs'' ▸ hE'
    have hfu : s'.funcs = s.funcs := by rw [← hs'', hF.2.1]
    obtain ⟨s₃, h₃⟩ := ih hE₁ hσ' (hostFn_funcs hfu hS) (hostFn_funcs hfu hU) hcs hr
    have h₁ : Steps P (s1Host mem) ⟨s, f, expression c ++ expression cs⟩
        ⟨s', f, expression cs⟩ := by
      simpa only [List.reverse_nil, vals, List.map_nil, List.nil_append] using
        exec_sound (P := P) (host := s1Host mem) (expression cs) he
    refine ⟨s₃, ?_⟩
    rw [← hcode', hcc, show ∀ a b : List Instr, expression (a ++ b) = expression a ++ expression b
      from fun a b => List.map_append ..]
    exact h₁.trans h₃
  | @sys s f args r v w p rest evs ha hrip hans _ ih =>
    show ∃ s₃, Steps P (s1Host mem) ⟨s, f, expression code⟩ ⟨s₃, f, expression codeR⟩
    obtain ⟨cs, hcs, hcode'⟩ : ∃ cs, emitItems sx ux p = some cs ∧ sysCode sx ux ++ cs = code := by
      simpa only [emitItems, Option.map_eq_some_iff] using hcode
    have hargs : args = sysRegs.map σ.read := Option.some.inj (ha.symm.trans (sysArgs_enc hE))
    have hr' : r = σ.rip := val_i64_inj.mp (Option.some.inj (hrip.symm.trans hE.2.2.1))
    have hfu : (sysStore s f r v w).funcs = s.funcs := sysStore_funcs s f r v w
    have hE₁ : Enc (sysStore s f r v w) f (sysCore σ v w) := hr' ▸ enc_sysStore_any hE v w
    obtain ⟨s₃, h₃⟩ := ih hE₁ (flagsDef_sysCore hσ v w)
      (hostFn_funcs hfu hS) (hostFn_funcs hfu hU) hcs hr
    have h₁ : Steps P (s1Host mem) ⟨s, f, expression (sysCode sx ux) ++ expression cs⟩
        ⟨sysStore s f r v w, f, expression cs⟩ := hr' ▸ sys_steps hS hU hE (hargs ▸ hans) _
    refine ⟨s₃, ?_⟩
    rw [← hcode', show ∀ a b : List Instr, expression (a ++ b) = expression a ++ expression b
      from fun a b => List.map_append ..]
    exact h₁.trans h₃
  | @pending s f args p ha =>
    have hcc : codeR = code := Option.some.inj (hr.symm.trans hcode)
    exact ⟨s, by rw [hcc]⟩

end Silmaril.Sim.WasiBridge.G
