module

public import Silmaril.Sim.Reduce.PCalls.Defs
public import Silmaril.Sim.X86.GCert.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# P-calls soundness for the certified G fragment: proofs

The header is `Silmaril/Sim/Reduce/PCalls/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.PCalls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GCert
open Silmaril.Wasm.Logic.Hoare (FSpecValid HWP)
open Silmaril.X86 (Reg State)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A store that differs only in its globals has the same functions. -/
theorem frames_funcs {s s' : Store H} {f : Frame} (h : Frames s s' f) : s'.funcs = s.funcs := by
  rw [h.2.1]

theorem stepFns_congr {s t : Store H} (hst : t.funcs = s.funcs) {f : Frame} {mi : ModuleInst}
    {p : XProg} {xs : List FuncIdx} (h : StepFns s f mi p xs) : StepFns t f mi p xs := by
  induction p generalizing xs with
  | nil => cases xs <;> simp_all [StepFns]
  | cons x p ih =>
    obtain ⟨i, len⟩ := x
    cases xs with
    | nil => exact h.elim
    | cons y ys =>
      obtain ⟨⟨a, fi, func, h₁, h₂, h₃⟩, h'⟩ := h
      exact ⟨⟨a, fi, func, h₁, hst ▸ h₂, h₃⟩, ih h'⟩

/-- **The method pieces from a concrete simulator**: functions running `emit i len` meet the
step specifications (`Silmaril.Sim.X86.GCert.step_valid`). -/
theorem stepCtx_of_stepFns {s : Store H} {f : Frame} {mi : ModuleInst} {p : XProg}
    {xs : List FuncIdx} (h : StepFns s f mi p xs) : StepCtx P host s f mi p xs := by
  induction p generalizing xs with
  | nil => cases xs <;> simp_all [StepFns, StepCtx]
  | cons x p ih =>
    obtain ⟨i, len⟩ := x
    cases xs with
    | nil => exact h.elim
    | cons y ys =>
      obtain ⟨⟨a, fi, func, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩, h'⟩ := h
      exact ⟨⟨a, fi, h₁, h₂, h₃, step_valid_of h₄ h₅ h₇ h₆⟩, ih h'⟩

/-- A program `(i, len) :: p` that runs retires its first instruction and runs the rest. -/
private theorem runExt_cons_some {i : Silmaril.X86.Ext.Instr} {len : Nat} {p : XProg}
    {σ : State} {m : Silmaril.Process.Memory} {r : State × Silmaril.Process.Memory}
    (h : runExt ((i, len) :: p) σ m = some r) :
    ∃ σ₁ m₁, Silmaril.X86.Ext.exec i σ m len = .ok σ₁ m₁ ∧ runExt p σ₁ m₁ = some r := by
  simp only [runExt] at h
  split at h
  next σ₁ m₁ hx₁ => exact ⟨σ₁, m₁, hx₁, h⟩
  next => exact absurd h (by simp)

/-- **A P-calls run exists**: from a store encoding `σ`, the P-calls body of a program that
retires runs to a store encoding the result. -/
theorem calls_wp {p : XProg} {xs : List FuncIdx} {s : Store H} {f : Frame} {mi : ModuleInst}
    (hfns : StepFns s f mi p xs) {σ σ' : State} {m m' : Silmaril.Process.Memory}
    (hE : Enc s (simFrame mi) σ) (hx : runExt p σ m = some (σ', m')) :
    Silmaril.Wasm.Logic.Core.WP P host s f (expression (callsCode xs))
      fun s' f' o => o = .normal [] ∧ f' = f ∧ Enc s' (simFrame mi) σ' := by
  induction p generalizing xs s σ m with
  | nil =>
    cases xs with
    | nil =>
      have hσ : σ = σ' ∧ m = m' := by
        simpa only [runExt, Option.some.injEq, Prod.mk.injEq] using hx
      rw [← hσ.1]
      exact Silmaril.Wasm.Logic.Core.wp_vals (vs := []) ⟨rfl, rfl, hE⟩
    | cons => exact hfns.elim
  | cons x p ih =>
    show Silmaril.Wasm.Logic.Core.WP P host s f (expression (callsCode xs)) _
    obtain ⟨i, len⟩ := x
    cases xs with
    | nil => exact hfns.elim
    | cons y ys =>
      show Silmaril.Wasm.Logic.Core.WP P host s f
        (vals ([] ++ []) ++ .plain (.call y) :: expression (callsCode ys)) _
      obtain ⟨⟨a, fi, func, hy, hs, hmod, hcode, hty, hloc, hbody⟩, hrest⟩ := hfns
      obtain ⟨σ₁, m₁, hx₁, hx'⟩ : ∃ σ₁ m₁, Silmaril.X86.Ext.exec i σ m len = .ok σ₁ m₁ ∧
          runExt p σ₁ m₁ = some (σ', m') := runExt_cons_some hx
      have hspec : Silmaril.Wasm.Logic.Core.FuncSpec P host a (cmdPre fi a [])
          (fun s args s' res => res = [] ∧ cmdPost fi i len s s') :=
        (straight_spec (P := P) (host := host) (a := a) hcode
          (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? hty) rfl (fun _ _ h => h.1)
          (fun _ _ h => by rw [h.2.1]; rfl) (step_ex hloc hbody)).2
      have hpre : cmdPre fi a [] s [] := ⟨hs, rfl, σ.read, by rw [hmod]; exact hE.gregs⟩
      refine Silmaril.Wasm.Logic.Core.wp_call hy (by rw [hs]; rfl) hspec hpre ?_
      intro s₁ res ⟨hres, hF, hpost⟩
      have hE₁ : Enc s₁ (simFrame mi) σ₁ := by
        rw [← hmod]; exact hpost σ σ₁ m m₁ (by rw [hmod]; exact hE) hx₁
      have hrest₁ : StepFns s₁ f mi p ys := stepFns_congr (frames_funcs hF) hrest
      simpa [vals, hres] using ih hrest₁ hE₁ hx'

/-- The every-run call rule for a step method. -/
theorem hwp_call_step {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {i : Silmaril.X86.Ext.Instr} {len : Nat} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : FSpecValid P host a (stepSpec fi a i len)) (hpre : cmdPre fi a [] s [])
    (hk : ∀ s', cmdPost fi i len s s' → HWP P host s' f rest Q) :
    HWP P host s f (.plain (.call x) :: rest) Q := by
  intro N
  cases N with
  | zero => trivial
  | succ N =>
    have := Silmaril.Wasm.Logic.Hoare.Safe.callIdx (vs₀ := []) (args := []) (rest := rest) (Q := Q)
      hx hf (hS N) hpre ?_
    · simpa [vals] using this
    · rintro s' o ⟨-, ⟨res, rfl, hres, hpost⟩ | ⟨rfl, h, -⟩ | ⟨b, rfl, h, -⟩⟩
      · cases hres
        simpa [Silmaril.Wasm.Logic.Hoare.seqPostK, vals] using hk s' hpost N
      · cases h
      · cases h

/-- **P-calls transfer**: a solved piece and a concrete simulator instance (in which the store
can be loaded with any state: the instance's globals are `0..22`) solve the x86 problem. -/
theorem xproblem_of_piece {p : XProg} {xs : List FuncIdx} {Pre : (Reg → BitVec 64) → Prop}
    {Post : (Reg → BitVec 64) → (Reg → BitVec 64) → Prop}
    (hW : Piece P host p xs Pre Post) {s : Store H} {f : Frame} {mi : ModuleInst}
    (hglob : mi.globals = List.range 23) (hfns : StepFns s f mi p xs) :
    XProblem p Pre Post := by
  intro σ σ' m m' hpre hx
  let t : Store H := { s with globals := (encStore (H := H) σ).globals }
  have hE : Enc t (simFrame mi) σ :=
    enc_congr (s := encStore (H := H) σ) (f := encFrame) (by simp [encFrame, simFrame, Frame.forCall, hglob]) rfl (enc_encStore σ)
  have hfns' : StepFns t f mi p xs := stepFns_congr (s := s) (t := t) rfl hfns
  obtain ⟨s', f', c', o, hsteps, hends, ho, -, hE'⟩ := calls_wp (P := P) (host := host) hfns' hE hx
  subst ho
  have hc' : c' = vals [] := hends
  subst hc'
  obtain ⟨-, hq⟩ := Silmaril.Wasm.Logic.Hoare.HWP.sound_vals
    (hW t f mi σ.read (stepCtx_of_stepFns hfns') hE.gregs hpre) hsteps
  exact hq σ'.read hE'.2.1

@[deprecated xproblem_of_piece (since := "2026-11-10")] alias reduce := xproblem_of_piece

end Silmaril.Sim.Reduce.PCalls
