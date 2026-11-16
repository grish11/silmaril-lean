module

public import Silmaril.Proofs.Sim.X86.G.Prog
public import Silmaril.X86.Ext.Machine

/-!
# From `runExt` to the bytes: the `Silmaril.X86.Ext` machine

`runExt p` executes decoded instructions. Here they are fetched: `CodeAt mem a p` says that the
memory decodes, from address `a` on, to the instructions of `p` one after the other (each
fetched as an executable span, `Silmaril.X86.Ext.fetch`). For a program the simulator
translates (`emitProg p = some code`), every retiring `runExt` run is a run of the machine's
`stepOpt exit` for `p.length` steps, ending at the address after the code (`run_of_runExt`).
`BytesAt` states code placement as byte spans, `codeAt_of_bytesAt` turns it into `CodeAt`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.X86.Ext (fetch Fetch)
open Silmaril.Process (Memory)

theorem codeAt_of_bytesAt {mem : Memory} {a : Word} {p : XProg} {bss : List (List Byte)}
    (hlen : p.length = bss.length)
    (hdec : ∀ (k : Nat) (h₁ : k < p.length) (h₂ : k < bss.length),
      Silmaril.X86.Ext.decode bss[k] = some p[k] ∧ p[k].2 = bss[k].length)
    (hb : BytesAt mem a bss) : CodeAt mem a p := by
  induction p generalizing a bss with
  | nil => trivial
  | cons x p ih =>
    obtain ⟨i, n⟩ := x
    cases bss with
    | nil => simp at hlen
    | cons bs bss =>
      obtain ⟨hd, hn⟩ := hdec 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hd hn
      obtain ⟨hf, hb'⟩ := hb
      refine ⟨Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bs, by rw [hn]; exact hf, hd⟩, ?_⟩
      rw [hn]
      exact ih (by simpa using hlen) (fun k h₁ h₂ => by
        have := hdec (k + 1) (by simpa using h₁) (by simpa using h₂)
        simpa only [List.getElem_cons_succ] using this) hb'

theorem codeAt_append {mem : Memory} {a : Word} {p q : XProg} (h : CodeAt mem a (p ++ q)) :
    CodeAt mem a p ∧ CodeAt mem (endAddr a p) q := by
  induction p generalizing a with
  | nil => exact ⟨trivial, h⟩
  | cons x p ih =>
    obtain ⟨i, n⟩ := x
    obtain ⟨hf, h'⟩ := h
    obtain ⟨h₁, h₂⟩ := ih h'
    exact ⟨⟨hf, h₁⟩, h₂⟩

/-- One retiring instruction of a translated program is one machine step. -/
theorem stepOpt_of_emit {i : Silmaril.X86.Ext.Instr} {n : Nat} {c : List Silmaril.Wasm.Instr}
    (hc : emit i n = some c) (exit : Word) {σ σ₁ : State} {mem m₁ : Memory}
    (hf : fetch mem σ.rip.toNat = .decoded i n) (hx : Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ m₁) :
    Silmaril.X86.Ext.stepOpt exit ⟨σ, mem⟩ = some ⟨σ₁, mem⟩ ∧ m₁ = mem ∧
      σ₁.rip = σ.rip + BitVec.ofNat 64 n := by
  obtain ⟨hrip, hnr, hm⟩ : σ₁.rip = σ.rip + BitVec.ofNat 64 n ∧ i ≠ .ret ∧ m₁ = mem := emit_rip hc hx
  have hn : n = i.length := Silmaril.X86.Ext.fetch_length hf
  have hstep : Silmaril.X86.Ext.stepOpt exit ⟨σ, mem⟩ = some ⟨σ₁, mem⟩ := by
    rw [Silmaril.X86.Ext.stepOpt_eq_some_iff]
    simp only [Silmaril.X86.Ext.step, hf]
    rw [← hn, hx, hm]
    simp [hnr]
  exact ⟨hstep, hm, hrip⟩

theorem runExt_cons {i : Silmaril.X86.Ext.Instr} {n : Nat} {p : XProg} {σ : State} {mem : Memory}
    {r : State × Memory} (hx : runExt ((i, n) :: p) σ mem = some r) :
    ∃ σ₁ m₁, Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ m₁ ∧ runExt p σ₁ m₁ = some r := by
  simp only [runExt] at hx
  split at hx
  next σ₁ m₁ he => exact ⟨σ₁, m₁, he, hx⟩
  next => cases hx

/-- **Machine runs of a translated program.** -/
theorem run_of_runExt {p : XProg} {code : List Silmaril.Wasm.Instr} (hc : emitProg p = some code)
    (exit : Word) {σ σ' : State} {mem mem' : Memory} (hcode : CodeAt mem σ.rip p)
    (hx : runExt p σ mem = some (σ', mem')) :
    Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) p.length ⟨σ, mem⟩ = some ⟨σ', mem'⟩ ∧
      σ'.rip = endAddr σ.rip p := by
  induction p generalizing σ mem code with
  | nil =>
    have h : σ = σ' ∧ mem = mem' := by simpa only [runExt, Option.some.injEq, Prod.mk.injEq] using hx
    exact ⟨by rw [← h.1, ← h.2]; rfl, by rw [← h.1]; rfl⟩
  | cons x p ih =>
    show Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) (x :: p).length ⟨σ, mem⟩ =
      some ⟨σ', mem'⟩ ∧ σ'.rip = endAddr σ.rip (x :: p)
    obtain ⟨i, n⟩ := x
    obtain ⟨c₁, h₁, cs, h₂, -⟩ : ∃ c₁, emit i n = some c₁ ∧ ∃ cs, emitProg p = some cs ∧
        c₁ ++ cs = code := by
      simpa only [emitProg, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] using hc
    obtain ⟨hf, hcode'⟩ : fetch mem σ.rip.toNat = .decoded i n ∧
        CodeAt mem (σ.rip + BitVec.ofNat 64 n) p := hcode
    obtain ⟨σ₁, m₁, hx₁, hx'⟩ : ∃ σ₁ m₁, Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ m₁ ∧
        runExt p σ₁ m₁ = some (σ', mem') := runExt_cons hx
    obtain ⟨hstep, hm, hrip⟩ := stepOpt_of_emit h₁ exit hf hx₁
    have hcode₁ : CodeAt mem σ₁.rip p := by rw [hrip]; exact hcode'
    have hx₁' : runExt p σ₁ mem = some (σ', mem') := by rw [← hm]; exact hx'
    obtain ⟨hr, he⟩ : Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) p.length
        ⟨σ₁, mem⟩ = some ⟨σ', mem'⟩ ∧ σ'.rip = endAddr σ₁.rip p := ih h₂ hcode₁ hx₁'
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, Silmaril.Machine.Execution.run_succ, hstep, Option.bind_some]
      exact hr
    · rw [he, hrip]; rfl

end Silmaril.Sim.X86.G
