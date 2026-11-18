module

public import Silmaril.Sim.X86.GInst.Defs
public import Silmaril.Sim.X86.GCert.Thms
public import Silmaril.Sim.X86.Max.Thms
public import Silmaril.Sim.Institution.Thms

/-!
# The G reduction as institution transfer: proofs

* `defined_preserved`: supported instructions keep the modelled flags defined;
* `gview_eq`: on a store encoding a state with defined modelled flags, the simulator's view is
  the reference view;
* **`complete`**: the Wasm model is a complete simulator of the reference (`CoSimulation`);
* **`reduce_inst`**: every demonic sentence satisfied by the Wasm model is satisfied by the x86
  model, by `Silmaril.Sim.Institution.transfer_demonic` (along the identity signature morphism);
* `wasm_maxSen`: the Wasm model satisfies `maxSen` (from `Silmaril.Sim.X86.Max.wasm_solution`,
  the `wpc` proof of the P-inline code); **`x86_maxSen`**: the x86 model does.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GInst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Institution Silmaril.Sim.X86.G Silmaril.Sim.X86.GCert
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State)
open Silmaril.X86.Ext (Sz RM Cond Result writeRM readRM retire aluStep)

variable {H : Type}

/-- Supported instructions keep the modelled flags defined. -/
theorem defined_preserved {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emit i len = some code) {σ σ' : State} (hd : Defined σ.flags)
    {m m' : Silmaril.Process.Memory} (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    Defined σ'.flags := by
  obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp hc
  exact (core_shape (H := Nat) (f := {}) hcore hx).2.2.2.1 hd

theorem flag_view {o : Option Bool} {v : Option Val} (hd : o.isSome) (h : FlagEnc v o) :
    valBits v = o.map b64 := by
  obtain ⟨bit, rfl, ha⟩ := h
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hd
  simp only [Silmaril.X86.FlagValue.admits_some] at ha
  subst ha
  rfl

/-- On a store encoding a state with defined modelled flags, the views agree. -/
theorem gview_eq {mi : ModuleInst} {s : Store H} {σ : State}
    (hE : Enc s (frameOf mi) σ) (hd : Defined σ.flags) : gview mi s = xview σ := by
  obtain ⟨-, hr, hri, hc, hz, hs, ho⟩ := hE
  obtain ⟨dc, dz, ds, dov⟩ := hd
  funext l
  cases l with
  | reg r => simp only [gview, xview, hr r]; rfl
  | rip => simp only [gview, xview, hri]; rfl
  | cf => exact flag_view dc hc
  | zf => exact flag_view dz hz
  | sf => exact flag_view ds hs
  | of => exact flag_view dov ho

/-- `Enc` survives the concretization of a result whose modelled flags are defined. -/
theorem enc_concretize {s : Store H} {f : Frame} {σ' τ : State} (hE : Enc s f σ')
    (hd : Defined σ'.flags) (hc : Concretizes σ' τ) : Enc s f τ := by
  obtain ⟨hl, hr, hri, ⟨bc, gc, ac⟩, ⟨bz, gz, az⟩, ⟨bs, gs, as⟩, ⟨bo, go, ao⟩⟩ := hE
  obtain ⟨hregs, hrip, -, rc, -, -, rz, rs, ro, -⟩ := hc
  obtain ⟨dc, dz, ds, dov⟩ := hd
  have keep : ∀ {m c : Option Bool} {b : Bool}, m.isSome → FlagRefines m c →
      Silmaril.X86.FlagValue.Admits m b → Silmaril.X86.FlagValue.Admits c b := by
    intro m c b hm hr ha
    rcases hr with rfl | rfl
    · simp at hm
    · exact ha
  refine ⟨hl, fun r => ?_, ?_, ⟨bc, gc, keep dc rc ac⟩, ⟨bz, gz, keep dz rz az⟩,
    ⟨bs, gs, keep ds rs as⟩, ⟨bo, go, keep dov ro ao⟩⟩
  · rw [hr r]; show _ = some (Val.i64 (τ.regs r)); rw [hregs]; rfl
  · rw [hri, hrip]

/-- **The G simulator is complete for the reference x86 model** (a `CoSimulation`): every
reference step from a loaded state is matched by a Wasm run of the generated code, with equal
views. `mi` lays the location globals out at `0..22`. -/
def coSim (P : Profile) (host : HostSemantics H) {mi : ModuleInst}
    (hmi : mi.globals = List.range 23) :
    CoSimulation (wasmM P host mi).machine ((Mod.reduct (Sig.Hom.id sig)).obj x86M).machine where
  R a b := Enc a.1 (frameOf mi) b.1.1
  view_eq {a b} h := gview_eq h b.2
  step {c a b b'} h hb := by
    rcases c with c | e
    · obtain ⟨σ', hx, hcon⟩ := hb
      obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp c.2
      obtain ⟨-, s', he, hE', -⟩ := emit_sound hcode h hx
      have hd' := defined_preserved hcode b.2 hx
      have hE'' := enc_concretize hE' hd' hcon
      have hs := Silmaril.Wasm.Logic.Core.exec_sound (P := P) (host := host) (rest := []) he
      simp only [List.reverse_nil, List.append_nil] at hs
      refine ⟨⟨s', ⟨_, hE''.gregs⟩⟩, ⟨code, hcode, by simpa [vals] using hs⟩, hE''⟩
    · exact e.elim
  load b := by
    have hg : (encFrame : Frame).module.globals = (frameOf mi).module.globals := by
      simp [encFrame, Frame.forCall, hmi]
    have hE : Enc (encStore (H := H) b.1.1) (frameOf mi) b.1.1 :=
      enc_congr (s := encStore (H := H) b.1.1) hg rfl (enc_encStore b.1.1)
    exact ⟨⟨encStore b.1.1, ⟨_, hE.gregs⟩⟩, hE⟩

/-- **The reduction as institution transfer**: every demonic sentence (partial
correctness of a program of instructions) that the Wasm model satisfies, the x86 model
satisfies (`Silmaril.Sim.Institution.transfer_demonic` along the identity morphism). -/
theorem reduce_inst (P : Profile) (host : HostSemantics H) {mi : ModuleInst}
    (hmi : mi.globals = List.range 23) {φ : Sen sig} (hφ : φ.IsDemonic)
    (h : sat (wasmM P host mi) φ) : sat x86M φ := by
  have := transfer_demonic (Sig.Hom.id sig) ⟨coSim P host hmi⟩ hφ h
  rwa [Sen.map_id] at this

/-! ## `max` -/

/-- The bits of a register global. -/
theorem valBits_i64 (x : BitVec 64) : valBits (some (Val.i64 x)) = some x := rfl

/-- Two straight-line runs to empty stacks compose into a run of the concatenated code. -/
private theorem steps_seq {P : Profile} {host : HostSemantics H} {s₁ s₂ s₃ : Store H}
    {f : Frame} {c₁ c₂ : List Instr}
    (h₁ : Steps P host ⟨s₁, f, expression c₁⟩ ⟨s₂, f, vals []⟩)
    (h₂ : Steps P host ⟨s₂, f, expression c₂⟩ ⟨s₃, f, vals []⟩) :
    Steps P host ⟨s₁, f, expression (c₁ ++ c₂)⟩ ⟨s₃, f, vals []⟩ := by
  have h₁' : Steps P host ⟨s₁, f, expression c₁ ++ expression c₂⟩ ⟨s₂, f, expression c₂⟩ := by
    simpa only [vals, List.map_nil, List.nil_append] using
      Silmaril.Wasm.Logic.Core.Steps.append (expression c₂) h₁
  have hc : expression (c₁ ++ c₂) = expression c₁ ++ expression c₂ := by
    simp only [expression, List.map_append]
  rw [hc]
  exact h₁'.trans h₂

/-- **The Wasm model satisfies `maxSen`**: from the Wasm solution of `max`
(`Silmaril.Sim.X86.Max.wasm_solution`, by `wpc`). A run of the program in the Wasm model is a run
of `maxCode` (the pieces composed). -/
theorem wasm_maxSen (P : Profile) (host : HostSemantics H) (mi : ModuleInst) :
    sat (wasmM P host mi) maxSen := by
  rintro ⟨a, R, hR⟩ ⟨a₃, hw₃⟩ - hrun x y hx hy
  obtain ⟨b₁, ⟨c₁, hc₁, hs₁⟩, b₂, ⟨c₂, hc₂, hs₂⟩, b₃, ⟨c₃, hc₃, hs₃⟩, rfl⟩ := hrun
  have hc₁' : emit (.mov .q (.reg .rax) .rdi) 3 = some c₁ := hc₁
  have hc₂' : emit (.alu .q .cmp (.reg .rax) .rsi) 3 = some c₂ := hc₂
  have hc₃' : emit (.cmov .q .l .rax (.reg .rsi)) 4 = some c₃ := hc₃
  have hcode : c₁ ++ (c₂ ++ (c₃ ++ [])) = Silmaril.Sim.X86.Max.maxCode := by
    have h : emitProg Silmaril.Sim.X86.Max.maxProg = some (c₁ ++ (c₂ ++ (c₃ ++ []))) := by
      simp only [emitProg, Silmaril.Sim.X86.Max.maxProg, hc₁', hc₂', hc₃',
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    have h' : emitProg Silmaril.Sim.X86.Max.maxProg = some Silmaril.Sim.X86.Max.maxCode := rfl
    exact Option.some.inj (h.symm.trans h')
  have hall : Steps P host ⟨a, frameOf mi, expression Silmaril.Sim.X86.Max.maxCode⟩
      ⟨a₃, frameOf mi, vals []⟩ := by
    rw [← hcode, List.append_nil]
    exact steps_seq hs₁ (steps_seq hs₂ hs₃)
  obtain ⟨-, hpost⟩ := Silmaril.Wasm.Logic.Hoare.HWP.sound_vals
    (Silmaril.Sim.X86.Max.wasm_solution (P := P) (host := host) a (frameOf mi) R hR trivial) hall
  obtain ⟨R', ⟨-, hr', -⟩⟩ := hw₃
  obtain ⟨hmax, -⟩ := hpost R' hr'
  have hrdi : gview mi a (.reg .rdi) = some (R .rdi) := by
    simp only [gview]; rw [hR.2.1]; rfl
  have hrsi : gview mi a (.reg .rsi) = some (R .rsi) := by
    simp only [gview]; rw [hR.2.1]; rfl
  have hx' : R .rdi = x := Option.some.inj (hrdi.symm.trans hx)
  have hy' : R .rsi = y := Option.some.inj (hrsi.symm.trans hy)
  rw [← hx', ← hy']
  show valBits (gval a₃ _ (.reg .rax)) = _
  rw [hr', hmax]; rfl

/-- **`max` in the x86 model**, by institution transfer from the Wasm model: every
(concretizing) `Ext.exec` run of `max`'s body from a state with defined modelled flags ends with
`rax` the signed maximum of the initial `rdi` and `rsi`. -/
theorem x86_maxSen : sat x86M maxSen :=
  reduce_inst (H := Nat) Silmaril.Wasm.Logic.Hoare.detP (fun _ _ _ _ => False)
    (mi := (encFrame : Frame).module) rfl trivial (wasm_maxSen _ _ _)

end Silmaril.Sim.X86.GInst
