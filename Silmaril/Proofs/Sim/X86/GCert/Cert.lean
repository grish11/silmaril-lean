module

public import Silmaril.Sim.X86.GCert.Defs
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.Sim.Wasm.Thms
public import Silmaril.Wasm.Game.Signature.Defs
public import Silmaril.Sim.X86.GModule.Thms

/-!
# The G simulator as a `Silmaril.Sim` simulator: the certificate

* `step_valid`: a function instance running `emit i len` (a full step) meets `stepSpec`
  (`FSpecValid`, every profile and host relation);
* `progress_defined`: every supported instruction retires from a state with defined modelled
  flags;
* `Hyps`: the store layout the certificate assumes (instance globals `0..22`, the step methods
  at `addr c`);
* **`cert`**: `Silmaril.Sim.Wasm.ExportSim.Cert` of `exportSim` against `xRef`, with the relation
  "the store encodes the state and holds the methods"; **`sound`**: `Silmaril.Sim.Sound`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GCert

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Wasm Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)
open Silmaril.X86 (State Flags Reg)

variable {H : Type}

/-! ## Congruence of the encoding -/

theorem gval_congr {s t : Store H} {f g : Frame} (hg : f.module.globals = g.module.globals)
    (hs : s.globals = t.globals) (l : Loc) : gval s f l = gval t g l := by
  rw [gval_eq, gval_eq, hg, hs]

theorem layout_congr {s t : Store H} {f g : Frame} (hg : f.module.globals = g.module.globals)
    (hs : s.globals = t.globals) (h : Layout s f) : Layout t g :=
  ⟨fun l => by rw [← hg, ← hs]; exact h.addr l,
    fun l₁ l₂ a h₁ h₂ => h.inj l₁ l₂ a (hg ▸ h₁) (hg ▸ h₂)⟩

theorem enc_congr {s t : Store H} {f g : Frame} {σ : State}
    (hg : f.module.globals = g.module.globals) (hs : s.globals = t.globals) (h : Enc s f σ) :
    Enc t g σ := by
  obtain ⟨hl, hr, hri, hc, hz, hsf, ho⟩ := h
  refine ⟨layout_congr hg hs hl, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [← gval_congr hg hs] <;> first | exact hr r | assumption

/-! ## Progress and the step specification -/

variable {P : Profile} {host : HostSemantics H}

/-- **Straight-line exports**: if, from every store and arguments allowed by `Pre`, the body
evaluates (`exec`) to a store satisfying `Post`, the function meets the every-run specification
(`FSpecValid`) and the existential one (`FuncSpec`, a returning run exists), returning nothing. -/
theorem straight_spec {a : Nat} {fi : FuncInst H} {func : Func}
    {ps rs : Validation.Ty (.list .val)} (hcode : fi.code = .wasm func)
    (he : Validation.Expand fi.type (.func ps rs)) (hrs : rs.length = 0)
    {Pre : Store H → List Val → Prop} {Post : Store H → List Val → Store H → Prop}
    (hfi : ∀ s args, Pre s args → s.funcs[a]? = some fi)
    (hlen : ∀ s args, Pre s args → args.length = ps.length)
    (hex : ∀ s args, Pre s args → ∃ s' f', Silmaril.Wasm.Logic.Core.exec s
      (Frame.forCall fi.module args func.locals) [] func.body = some (s', f', []) ∧
      Post s args s') :
    FSpecValid P host a ⟨Pre, fun s args s' o => o = .normal [] ∧ Post s args s'⟩ ∧
      Silmaril.Wasm.Logic.Core.FuncSpec P host a Pre (fun s args s' res => res = [] ∧ Post s args s')
    := by
  refine ⟨Silmaril.Wasm.Examples.Common.FSpecValid.of_body_hwp hfi hcode he hlen fun s args h => ?_,
    Silmaril.Wasm.Logic.Core.FuncSpec.of_body hfi hcode he hlen fun s args h => ?_⟩
  · obtain ⟨s', f', hx, hp⟩ := hex s args h
    have hw := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .part) (P := P) (host := host)
      (vs := []) (rest := []) hx (Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .part) (P := P)
        (host := host) (vs := [])
        (Q := Silmaril.Wasm.Examples.Common.bodyPost rs.length (fun s'' o =>
          o = .normal [] ∧ Post s args s'')) ⟨by rw [hrs]; rfl, rfl, hp⟩)
    simpa [vals] using hw
  · obtain ⟨s', f', hx, hp⟩ := hex s args h
    refine Silmaril.Wasm.Logic.Core.wp_exec_all ?_
    rw [hx]
    exact ⟨by rw [hrs]; rfl, rfl, hp⟩

/-- The evaluation obligation of a full step method (body `emit i len`, no arguments). -/
theorem step_ex {fi : FuncInst H} {func : Func} {a : Nat} {i : Silmaril.X86.Ext.Instr}
    {len : Nat} (hloc : func.locals = []) (hbody : emit i len = some func.body) :
    ∀ s args, cmdPre fi a [] s args → ∃ s' f', Silmaril.Wasm.Logic.Core.exec s
      (Frame.forCall fi.module args func.locals) [] func.body = some (s', f', []) ∧
      cmdPost fi i len s s' := by
  rintro s args ⟨-, rfl, R, hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩
  rw [hloc]
  have hE := enc_stateOf hl hr hw hc hz hs ho
  obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨σ₀', hx₀⟩ := emitCore_progress hcore R w bc bz bs bo ⟨[], {}⟩ len
  obtain ⟨-, s₁, he, -, hF⟩ := emit_sound hbody hE hx₀
  refine ⟨s₁, _, he, hF, fun σ σ' m m' hEσ hx => ?_⟩
  obtain ⟨-, s₂, he₂, hE₂, -⟩ := emit_sound hbody hEσ hx
  rw [he] at he₂
  obtain rfl : s₁ = s₂ := by simp only [Option.some.injEq, Prod.mk.injEq] at he₂; exact he₂.1
  exact hE₂

/-- The evaluation obligation of an ABI method (body `emitCore i`, no arguments) for the
command `(i, 0)`: the instruction's effect with RIP unchanged. -/
theorem method_ex {fi : FuncInst H} {func : Func} {a : Nat} {i : Silmaril.X86.Ext.Instr}
    (hloc : func.locals = []) (hbody : emitCore i = some func.body) :
    ∀ s args, cmdPre fi a [] s args → ∃ s' f', Silmaril.Wasm.Logic.Core.exec s
      (Frame.forCall fi.module args func.locals) [] func.body = some (s', f', []) ∧
      cmdPost fi i 0 s s' := by
  rintro s args ⟨-, rfl, R, hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩
  rw [hloc]
  have hE := enc_stateOf hl hr hw hc hz hs ho
  obtain ⟨σ₀', hx₀⟩ := emitCore_progress hbody R w bc bz bs bo ⟨[], {}⟩ 0
  obtain ⟨-, s₁, he, -, hF⟩ := core_sound hbody hE hx₀
  refine ⟨s₁, _, he, hF, fun σ σ' m m' hEσ hx => ?_⟩
  obtain ⟨-, s₂, he₂, hE₂, -⟩ := core_sound hbody hEσ hx
  rw [he] at he₂
  obtain rfl : s₁ = s₂ := by simp only [Option.some.injEq, Prod.mk.injEq] at he₂; exact he₂.1
  have hrip := (emit_rip (code := func.body ++ nextCode 0) (by simp [emit, hbody]) hx).1
  have hσ : { σ' with rip := σ.rip } = σ' := by
    obtain ⟨regs, rip, fl, fs⟩ := σ'
    simp only at hrip ⊢
    rw [hrip]
    simp
  rw [hσ] at hE₂
  exact hE₂

/-- The body of `i_next`. -/
def nextBody : List Instr :=
  [gget .rip, .localGet ⟨0⟩, b64op .add, gset .rip]

/-- The state part of `i_next`: after `nop` of length `n` from a state encoded with RIP `w`,
the store with RIP `w + n` encodes the result. -/
private theorem next_post {s : Store H} {f : Frame} {w n : BitVec 64}
    (hw : gval s f .rip = some (Val.i64 w)) {σ σ' : State} {m m' : Silmaril.Process.Memory}
    (hEσ : Enc s f σ) (hx : Silmaril.X86.Ext.exec (.nop 0) σ m n.toNat = .ok σ' m') :
    Enc (upd s f .rip (Val.i64 (w + n))) f σ' := by
  have hx' : { σ with rip := σ.rip + BitVec.ofNat 64 n.toNat } = σ' ∧ m = m' := by
    simpa only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      Silmaril.X86.Ext.Result.ok.injEq] using hx
  have hrw : σ.rip = w := val_i64_inj.mp (Option.some.inj (hEσ.2.2.1.symm.trans hw))
  have hrip : σ.rip + BitVec.ofNat 64 n.toNat = w + n := by
    rw [hrw, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← hx'.1]
  exact hEσ.next { σ with rip := σ.rip + BitVec.ofNat 64 n.toNat } rfl rfl (w + n) hrip

/-- The evaluation obligation of `i_next` (body `nextBody`, argument `n : i64`): the command
`(nop, n)`, i.e. `rip += n`. -/
theorem next_ex {fi : FuncInst H} {func : Func} {a : Nat} (n : BitVec 64)
    (hloc : func.locals = []) (hbody : func.body = nextBody) :
    ∀ s args, cmdPre fi a [Val.i64 n] s args → ∃ s' f', Silmaril.Wasm.Logic.Core.exec s
      (Frame.forCall fi.module args func.locals) [] func.body = some (s', f', []) ∧
      cmdPost fi (.nop 0) n.toNat s s' := by
  rintro s args ⟨-, rfl, R, hl, hr, ⟨w, hw⟩, -⟩
  rw [hloc, hbody]
  have hl' : Layout s (Frame.forCall fi.module [Val.i64 n] []) := layout_congr (f := Frame.forCall fi.module [] [])
    (g := Frame.forCall fi.module [Val.i64 n] []) rfl rfl hl
  have hw' : gval s (Frame.forCall fi.module [Val.i64 n] []) .rip = some (Val.i64 w) := hw
  refine ⟨upd s (Frame.forCall fi.module [] []) .rip (Val.i64 (w + n)),
    Frame.forCall fi.module [Val.i64 n] [], ?_,
    (Frames.refl s (Frame.forCall fi.module [] [])).upd hl .rip _, fun σ σ' m m' hEσ hx => ?_⟩
  · simp only [nextBody, Silmaril.Wasm.Logic.Core.exec_cons, Silmaril.Wasm.Logic.Core.exec_nil,
      exec1_gget, hw', Option.map_some]
    rw [show Silmaril.Wasm.Logic.Core.exec1 s (Frame.forCall fi.module [Val.i64 n] [])
        [Val.i64 w] (.localGet ⟨0⟩) = some (s, _, [Val.i64 n, Val.i64 w]) from rfl]
    simp only [exec1_add, exec1_gset hl']
    rfl
  · exact next_post hw hEσ hx

/-- **A full step method meets `stepSpec`**, at every profile and for every host relation. -/
theorem step_valid {a : Nat} {fi : FuncInst H} {func : Func} {i : Silmaril.X86.Ext.Instr}
    {len : Nat} {ps rs : Validation.Ty (.list .val)} (hcode : fi.code = .wasm func)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0) (hrs : rs.length = 0)
    (hloc : func.locals = []) (hbody : emit i len = some func.body) :
    FSpecValid P host a (stepSpec fi a i len) :=
  (straight_spec hcode he hrs (fun _ _ h => h.1) (fun _ _ h => by rw [h.2.1, hps]; rfl)
    (step_ex hloc hbody)).1

/-! ## The certificate -/

variable {C : Type} {cmd : C → Silmaril.X86.Ext.Instr × Nat} {mi : ModuleInst} {addr : C → Nat}
  {args : C → List Val} {s₀ : Store H} {fi : C → FuncInst H}

/-- The certificate's relation: the store encodes the state and holds the base store's
functions. -/
def certR (mi : ModuleInst) (s₀ : Store H) (cmd : C → Silmaril.X86.Ext.Instr × Nat)
    (s : Store H) (b : (xRef cmd).St) : Prop :=
  Enc s (Frame.forCall mi [] []) b.1.1 ∧ s.funcs = s₀.funcs

theorem flagRefines_of_admits {m : Option Bool} {b : Bool}
    (h : Silmaril.X86.FlagValue.Admits m b) : FlagRefines m (some b) := by
  cases m with
  | none => exact .inl rfl
  | some x => exact .inr (by simp only [Silmaril.X86.FlagValue.admits_some] at h; rw [h])

theorem xview_flag {m : Option Bool} {bit : Bool} {v : BitVec 64} (hd : m.isSome)
    (ha : Silmaril.X86.FlagValue.Admits m bit) (hv : some (b64 bit) = some v) :
    m.map b64 = some v := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hd
  simp only [Silmaril.X86.FlagValue.admits_some] at ha
  subst ha
  exact hv

/-- **The certificate**: the G simulator (full step methods) is a certified `ExportSim` of the
reference machine `xRef cmd`. -/
def cert (h : Hyps P host cmd mi addr args s₀ fi) :
    (exportSim P host mi addr args).Cert (xRef cmd) where
  R := certR mi s₀ cmd
  view_le := by
    intro a b hR l v hv
    obtain ⟨⟨-, hr, hri, ⟨bc, hc, ac⟩, ⟨bz, hz, az⟩, ⟨bs, hs, as⟩, ⟨bo, ho, ao⟩⟩, -⟩ := hR
    obtain ⟨dc, dz, ds, dov⟩ := b.2
    simp only [exportSim, gview] at hv
    cases l with
    | reg r => rw [hr r] at hv; exact hv
    | rip => rw [hri] at hv; exact hv
    | cf => rw [hc] at hv; exact xview_flag dc ac hv
    | zf => rw [hz] at hv; exact xview_flag dz az hv
    | sf => rw [hs] at hv; exact xview_flag ds as hv
    | of => rw [ho] at hv; exact xview_flag dov ao hv
  load := by
    intro b
    have hg : (encFrame : Frame).module.globals = (Frame.forCall mi [] []).module.globals := by
      simp [encFrame, Frame.forCall, h.globals]
    let a : Store H := { s₀ with globals := (encStore (H := H) b.1.1).globals }
    refine ⟨a, ⟨enc_congr (s := encStore (H := H) b.1.1) hg rfl (enc_encStore b.1.1), rfl⟩,
      funext fun l => ?_⟩
    obtain ⟨dc, dz, ds, dov⟩ := b.2
    simp only [exportSim, gview]
    have hgv : gval a (Frame.forCall mi [] []) l = gval (encStore (H := H) b.1.1) encFrame l :=
      (gval_congr hg rfl l).symm
    rw [hgv, gval_encStore]
    cases l with
    | reg r =>
      have : r.toBitVec.toNat < 16 := r.toBitVec.isLt
      simp only [Loc.idx, encVal, this, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        Reg.ofBitVec_toBitVec]
      rfl
    | rip => rfl
    | cf => obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp dc; simp [xRef, xview, Loc.idx, encVal, hx]; rfl
    | zf => obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp dz; simp [xRef, xview, Loc.idx, encVal, hx]; rfl
    | sf => obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ds; simp [xRef, xview, Loc.idx, encVal, hx]; rfl
    | of => obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp dov; simp [xRef, xview, Loc.idx, encVal, hx]; rfl
  method := by
    intro c b s s' f' res hR hok hs
    obtain ⟨hE, hfs⟩ := hR
    have hfr : Frame.forCall (fi c).module [] [] = Frame.forCall mi [] [] := by rw [h.module c]
    have hpre : (cmdSpec (fi c) (addr c) (args c) (cmd c).1 (cmd c).2).pre s (args c) :=
      ⟨by rw [hfs]; exact h.funcs c, rfl, _, hfr ▸ hE.gregs⟩
    obtain ⟨-, hF, hall⟩ := Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals (h.valid c) hpre hs
    obtain ⟨σ', hx⟩ := h.progress c b.1.1 b.1.2 b.2
    have hE' := hall b.1.1 σ' b.1.2 b.1.2 (hfr ▸ hE) hx
    rw [hfr] at hE' hF
    obtain ⟨hl', hr', hri', ⟨bc, hc, ac⟩, ⟨bz, hz, az⟩, ⟨bs, hsg, as⟩, ⟨bo, ho, ao⟩⟩ := hE'
    let τ : State := { σ' with flags := ⟨some bc, σ'.flags.parity, σ'.flags.adjust, some bz,
      some bs, some bo⟩ }
    refine ⟨⟨(τ, b.1.2), rfl, rfl, rfl, rfl⟩, ⟨σ', hx, rfl, rfl, rfl,
      flagRefines_of_admits ac, .inr rfl, .inr rfl, flagRefines_of_admits az,
      flagRefines_of_admits as, flagRefines_of_admits ao, rfl, rfl, rfl, rfl⟩,
      ⟨⟨hl', hr', hri', ⟨bc, hc, rfl⟩, ⟨bz, hz, rfl⟩, ⟨bs, hsg, rfl⟩, ⟨bo, ho, rfl⟩⟩, ?_⟩⟩
    rw [← hfs, hF.2.1]

/-- **The G simulator is sound** in the sense of `Silmaril.Sim.Sound`: its machine
(calls of the step exports) is simulated by the reference x86 machine `xRef cmd`. -/
theorem sound (h : Hyps P host cmd mi addr args s₀ fi) :
    Silmaril.Sim.Sound (exportSim P host mi addr args).toWasmSim.toMachine (xRef cmd) :=
  (cert h).sound

/-! ## The concrete instance: `stepModule` -/

/-- A full step function instance of the right shape meets its command specification. -/
theorem step_valid_of {a : Nat} {fi : FuncInst H} {func : Func} {i : Silmaril.X86.Ext.Instr}
    {len : Nat} (h₁ : fi.code = .wasm func)
    (h₂ : Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ⟨[], []⟩)
    (h₃ : emit i len = some func.body) (h₄ : func.locals = []) :
    FSpecValid P host a (cmdSpec fi a [] i len) :=
  step_valid h₁ (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? h₂) rfl rfl h₄ h₃

/-- The instantiated `stepModule` meets the certificate's assumptions (layout by `rfl` and
`decide +kernel`). -/
theorem step_hyps (P : Profile) (host : HostSemantics Nat) : ∃ fi : Fin 3 → FuncInst Nat,
    Hyps P host maxCmd stepMI (fun c => c.val) (fun _ => []) stepStore fi := by
  have hlen : stepStore.funcs.length = 3 := rfl
  obtain ⟨f₀, f₁, f₂, hf⟩ : ∃ f₀ f₁ f₂, stepStore.funcs = [f₀, f₁, f₂] := by
    match h : stepStore.funcs, hlen with
    | [f₀, f₁, f₂], _ => exact ⟨f₀, f₁, f₂, rfl⟩
  have hc : stepStore.funcs.map FuncInst.code =
      [.wasm stepModule.funcs[0], .wasm stepModule.funcs[1], .wasm stepModule.funcs[2]] := rfl
  have hm : stepStore.funcs.map FuncInst.module = [stepMI, stepMI, stepMI] := rfl
  have ht : stepStore.funcs.map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      [some ⟨[], []⟩, some ⟨[], []⟩, some ⟨[], []⟩] := by decide +kernel
  obtain ⟨hc₀, hc₁, hc₂⟩ : f₀.code = .wasm stepModule.funcs[0] ∧
      f₁.code = .wasm stepModule.funcs[1] ∧ f₂.code = .wasm stepModule.funcs[2] := by
    simpa only [hf, List.map_cons, List.map_nil, List.cons.injEq, and_true] using hc
  obtain ⟨hm₀, hm₁, hm₂⟩ : f₀.module = stepMI ∧ f₁.module = stepMI ∧ f₂.module = stepMI := by
    simpa only [hf, List.map_cons, List.map_nil, List.cons.injEq, and_true] using hm
  obtain ⟨ht₀, ht₁, ht₂⟩ : Silmaril.Wasm.Game.FnType.ofDefType? f₀.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? f₁.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? f₂.type = some ⟨[], []⟩ := by
    simpa only [hf, List.map_cons, List.map_nil, List.cons.injEq, and_true] using ht
  refine ⟨fun c => match c with | 0 => f₀ | 1 => f₁ | 2 => f₂, ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    match k, hk with
    | 0, _ => rw [hf]; rfl
    | 1, _ => rw [hf]; rfl
    | 2, _ => rw [hf]; rfl
  · rintro ⟨k, hk⟩
    match k, hk with
    | 0, _ => exact hm₀
    | 1, _ => exact hm₁
    | 2, _ => exact hm₂
  · rintro ⟨k, hk⟩
    match k, hk with
    | 0, _ => exact step_valid_of hc₀ ht₀ rfl rfl
    | 1, _ => exact step_valid_of hc₁ ht₁ rfl rfl
    | 2, _ => exact step_valid_of hc₂ ht₂ rfl rfl
  · rintro ⟨k, hk⟩ σ m hd
    match k, hk with
    | 0, _ => exact progress_defined (core := [gget (.reg .rdi), gset (.reg .rax)]) rfl hd m 3
    | 1, _ => exact progress_defined (core := aluCode .cmp .rax .rsi) rfl hd m 3
    | 2, _ => exact progress_defined (core := cmovCode [gget .sf, gget .of, b64op .xor] .rax .rsi)
                rfl hd m 4

/-- **The step methods of `max`, instantiated, are a sound simulator** of the reference x86
machine on `max`'s three instructions (`Silmaril.Sim.Sound`), at every profile and for every host
relation. -/
theorem stepModule_sound (P : Profile) (host : HostSemantics Nat) :
    Silmaril.Sim.Sound
      (exportSim P host stepMI (fun c : Fin 3 => c.val) (fun _ => [])).toWasmSim.toMachine
      (xRef maxCmd) := by
  obtain ⟨fi, h⟩ := step_hyps P host
  exact sound h

/-! ## The ABI-style simulator `simModule`, instantiated -/

/-- The instantiated `simModule` (`Silmaril.Sim.X86.GModule.s₀`, `GModule.f₀`) meets the
certificate's assumptions for its seven exports (six methods, `i_next`). -/
theorem sim_hyps (P : Profile) (host : HostSemantics Nat) : ∃ fi : SCmd → FuncInst Nat,
    Hyps P host simCmd GModule.f₀.module simAddr simArgs GModule.s₀ fi := by
  have hlen : GModule.s₀.funcs.length = 8 := by decide
  obtain ⟨g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, hf⟩ :
      ∃ g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇, GModule.s₀.funcs = [g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇] := by
    match h : GModule.s₀.funcs, hlen with
    | [g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇], _ => exact ⟨g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, rfl⟩
  have hc : GModule.s₀.funcs.map FuncInst.code =
      simModule.funcs.map FuncCode.wasm := rfl
  have hm : GModule.s₀.funcs.map FuncInst.module = List.replicate 8 GModule.f₀.module := by decide
  have ht : (GModule.s₀.funcs.take 7).map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      List.replicate 6 (some ⟨[], []⟩) ++ [some ⟨[.num (.int .i64)], []⟩] := by decide +kernel
  have hb : (simModule.funcs.take 7).map (·.body) =
      [[gget (.reg .rdi), gset (.reg .rax)], aluCode .add .rax .rsi, aluCode .sub .rax .rsi,
        aluCode .xor .rax .rsi, aluCode .cmp .rax .rsi,
        cmovCode [gget .sf, gget .of, b64op .xor] .rax .rsi, nextBody] := rfl
  have hl : (simModule.funcs.take 7).map (·.locals) = List.replicate 7 [] := rfl
  obtain ⟨u₀, u₁, u₂, u₃, u₄, u₅, u₆, u₇, hu⟩ :
      ∃ u₀ u₁ u₂ u₃ u₄ u₅ u₆ u₇, simModule.funcs = [u₀, u₁, u₂, u₃, u₄, u₅, u₆, u₇] := by
    have : simModule.funcs.length = 8 := rfl
    match h : simModule.funcs, this with
    | [u₀, u₁, u₂, u₃, u₄, u₅, u₆, u₇], _ => exact ⟨u₀, u₁, u₂, u₃, u₄, u₅, u₆, u₇, rfl⟩
  obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, c₆, -⟩ : g₀.code = .wasm u₀ ∧ g₁.code = .wasm u₁ ∧
      g₂.code = .wasm u₂ ∧ g₃.code = .wasm u₃ ∧ g₄.code = .wasm u₄ ∧ g₅.code = .wasm u₅ ∧
      g₆.code = .wasm u₆ ∧ g₇.code = .wasm u₇ := by
    simpa only [hf, hu, List.map_cons, List.map_nil, List.cons.injEq, and_true] using hc
  obtain ⟨m₀, m₁, m₂, m₃, m₄, m₅, m₆, -⟩ : g₀.module = GModule.f₀.module ∧
      g₁.module = GModule.f₀.module ∧ g₂.module = GModule.f₀.module ∧ g₃.module = GModule.f₀.module ∧
      g₄.module = GModule.f₀.module ∧ g₅.module = GModule.f₀.module ∧ g₆.module = GModule.f₀.module ∧
      g₇.module = GModule.f₀.module := by
    simpa only [hf, List.map_cons, List.map_nil, List.cons.injEq, List.replicate, and_true]
      using hm
  obtain ⟨t₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ :
      Silmaril.Wasm.Game.FnType.ofDefType? g₀.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₁.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₂.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₃.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₄.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₅.type = some ⟨[], []⟩ ∧
      Silmaril.Wasm.Game.FnType.ofDefType? g₆.type = some ⟨[.num (.int .i64)], []⟩ := by
    simpa only [hf, List.map_cons, List.map_nil, List.cons.injEq, List.take, List.replicate,
      List.cons_append, List.nil_append, and_true] using ht
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆⟩ : u₀.body = [gget (.reg .rdi), gset (.reg .rax)] ∧
      u₁.body = aluCode .add .rax .rsi ∧ u₂.body = aluCode .sub .rax .rsi ∧
      u₃.body = aluCode .xor .rax .rsi ∧ u₄.body = aluCode .cmp .rax .rsi ∧
      u₅.body = cmovCode [gget .sf, gget .of, b64op .xor] .rax .rsi ∧ u₆.body = nextBody := by
    simpa only [hu, List.map_cons, List.map_nil, List.cons.injEq, List.take, and_true] using hb
  obtain ⟨l₀, l₁, l₂, l₃, l₄, l₅, l₆⟩ : u₀.locals = [] ∧ u₁.locals = [] ∧ u₂.locals = [] ∧
      u₃.locals = [] ∧ u₄.locals = [] ∧ u₅.locals = [] ∧ u₆.locals = [] := by
    simpa only [hu, List.map_cons, List.map_nil, List.cons.injEq, List.take, List.replicate,
      and_true] using hl
  have mv : ∀ {a : Nat} {fi : FuncInst Nat} {func : Func} {i : Silmaril.X86.Ext.Instr},
      fi.code = .wasm func → Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ⟨[], []⟩ →
      emitCore i = some func.body → func.locals = [] →
      FSpecValid P host a (cmdSpec fi a [] i 0) := fun h₁ h₂ h₃ h₄ =>
    (straight_spec h₁ (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? h₂) rfl (fun _ _ h => h.1)
      (fun _ _ h => by rw [h.2.1]; rfl) (method_ex h₄ h₃)).1
  refine ⟨fun c => match c with
    | .m 0 => g₀ | .m 1 => g₁ | .m 2 => g₂ | .m 3 => g₃ | .m 4 => g₄ | .m 5 => g₅
    | .next _ => g₆, ⟨Silmaril.Sim.X86.GModule.f₀_globals, ?_, ?_, ?_, ?_⟩⟩
  · show ∀ c, GModule.s₀.funcs[simAddr c]? = some _
    rintro (⟨k, hk⟩ | n)
    · match k, hk with
      | 0, _ => rw [hf]; rfl
      | 1, _ => rw [hf]; rfl
      | 2, _ => rw [hf]; rfl
      | 3, _ => rw [hf]; rfl
      | 4, _ => rw [hf]; rfl
      | 5, _ => rw [hf]; rfl
    · rw [hf]; rfl
  · show ∀ c, FuncInst.module _ = GModule.f₀.module
    rintro (⟨k, hk⟩ | n)
    · match k, hk with
      | 0, _ => exact m₀
      | 1, _ => exact m₁
      | 2, _ => exact m₂
      | 3, _ => exact m₃
      | 4, _ => exact m₄
      | 5, _ => exact m₅
    · exact m₆
  · show ∀ c, FSpecValid P host (simAddr c) (cmdSpec _ (simAddr c) (simArgs c) (simCmd c).1
      (simCmd c).2)
    rintro (⟨k, hk⟩ | n)
    · match k, hk with
      | 0, _ => exact mv c₀ t₀ (by rw [b₀]; rfl) l₀
      | 1, _ => exact mv c₁ t₁ (by rw [b₁]; rfl) l₁
      | 2, _ => exact mv c₂ t₂ (by rw [b₂]; rfl) l₂
      | 3, _ => exact mv c₃ t₃ (by rw [b₃]; rfl) l₃
      | 4, _ => exact mv c₄ t₄ (by rw [b₄]; rfl) l₄
      | 5, _ => exact mv c₅ t₅ (by rw [b₅]; rfl) l₅
    · exact (straight_spec c₆ (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? t₆) rfl
        (fun _ _ h => h.1) (fun _ _ h => by rw [h.2.1]; rfl) (next_ex n l₆ b₆)).1
  · show ∀ c (σ : State) m, Defined σ.flags →
      ∃ σ', Silmaril.X86.Ext.exec (simCmd c).1 σ m (simCmd c).2 = .ok σ' m
    rintro (⟨k, hk⟩ | n) σ m hd
    · show ∃ σ', Silmaril.X86.Ext.exec (simInstr ⟨k, hk⟩) σ m 0 = .ok σ' m
      match k, hk with
      | 0, _ => exact progress_defined (core := [gget (.reg .rdi), gset (.reg .rax)]) rfl hd m 0
      | 1, _ => exact progress_defined (core := aluCode .add .rax .rsi) rfl hd m 0
      | 2, _ => exact progress_defined (core := aluCode .sub .rax .rsi) rfl hd m 0
      | 3, _ => exact progress_defined (core := aluCode .xor .rax .rsi) rfl hd m 0
      | 4, _ => exact progress_defined (core := aluCode .cmp .rax .rsi) rfl hd m 0
      | 5, _ =>
        exact progress_defined (core := cmovCode [gget .sf, gget .of, b64op .xor] .rax .rsi)
          rfl hd m 0
    · exact ⟨_, rfl⟩

/-- **`simModule` is a certified `ExportSim`**: its machine (calls of the six
methods and `i_next` in the instantiated store) is a sound simulator of the reference x86
machine on `simCmd` (methods = instructions at length `0`, `i_next n` = a NOP of length `n`),
at every profile and for every host relation. -/
theorem simModule_sound (P : Profile) (host : HostSemantics Nat) :
    Silmaril.Sim.Sound (exportSim P host GModule.f₀.module simAddr simArgs).toWasmSim.toMachine
      (xRef simCmd) := by
  obtain ⟨fi, h⟩ := sim_hyps P host
  exact sound h

end Silmaril.Sim.X86.GCert
