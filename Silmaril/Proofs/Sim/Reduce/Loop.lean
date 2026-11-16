module

public import Silmaril.Sim.Reduce.Loop.Defs
public import Silmaril.Sim.X86.Loop.Thms
public import Silmaril.Sim.X86.GCert.Thms
public import Silmaril.X86.Ext.SymExec

/-!
# Termination and frame of dispatcher runs from Wasm rankings: proofs

The header is `Silmaril/Sim/Reduce/Loop/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Loop

open Silmaril.X86 (Reg Word State)
open Silmaril.X86.Ext
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
/-- **Frame, per instruction form**: a method's instruction changes no register outside
`writesOf`. -/
theorem frame_of_exec {i : Instr} {n : Nat} {code : List Silmaril.Wasm.Instr} (hc : emitX i n = some code)
    {σ σ' : State} {m m' : Silmaril.Process.Memory} (hx : exec i σ m n = .ok σ' m') :
    ∀ r, r ∉ writesOf i → σ'.read r = σ.read r := by
  intro r hr
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, -, -⟩ | ⟨rel, rfl, -⟩ | he
  · simp only [exec] at hx
    split at hx <;> simp at hx <;> (obtain ⟨rfl, -⟩ := hx; rfl)
  · simp [exec] at hx; obtain ⟨rfl, -⟩ := hx; rfl
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    rcases emitCore_cases hcore with ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨d, imm, rfl, -⟩ |
      ⟨op, d, src, rfl, -⟩ | ⟨c, cc, d, src, rfl, -, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨d, rfl, -⟩ |
      ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ <;>
      simp [writesOf] at hr <;>
      simp [exec, readRM, writeRM, retire, aluStep] at hx <;>
      first
      | (obtain ⟨rfl, -⟩ := hx; first | rfl | exact State.read_write_other _ _ _ _ hr | simp [Sz.write, hr])
      | (split at hx <;> simp at hx <;> (try split at hx) <;> (try simp at hx) <;>
          (try obtain ⟨rfl, -⟩ := hx) <;> first | rfl | exact State.read_write_other _ _ _ _ hr |
            (rename_i h; split at h <;> simp at h <;> (obtain ⟨rfl, -⟩ := h) <;>
              first | rfl | exact State.read_write_other _ _ _ _ hr))

/-- **Progress**: every method's instruction retires from a state with defined flags. -/
theorem emitX_progress {i : Instr} {n : Nat} {code : List Silmaril.Wasm.Instr} (hc : emitX i n = some code)
    {σ : State} (hd : Defined σ.flags) (m : Silmaril.Process.Memory) :
    ∃ σ', exec i σ m n = .ok σ' m := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, hcc, -⟩ | ⟨rel, rfl, -⟩ | he
  · obtain ⟨regs, rip, ⟨cf, p, a, z, sg, o⟩, fs⟩ := σ
    obtain ⟨hc', hz', hs', ho'⟩ := hd
    obtain ⟨bc, rfl⟩ := Option.isSome_iff_exists.mp hc'
    obtain ⟨bz, rfl⟩ := Option.isSome_iff_exists.mp hz'
    obtain ⟨bs, rfl⟩ := Option.isSome_iff_exists.mp hs'
    obtain ⟨bo, rfl⟩ := Option.isSome_iff_exists.mp ho'
    cases c <;> simp only [condCode, reduceCtorEq] at hcc <;>
      cases bc <;> cases bz <;> cases bs <;> cases bo <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    exact progress_defined hcore hd m n

/-- **Progress** of instructions that read no flags. -/
theorem progress_nf {i : Instr} {n : Nat} {code : List Silmaril.Wasm.Instr} (hc : emitX i n = some code)
    (hr : readsFlags i = false) (σ : State) (m : Silmaril.Process.Memory) :
    ∃ σ', exec i σ m n = .ok σ' m := by
  rcases emitX_cases hc with ⟨c, cc, rel, hi, -, -⟩ | ⟨rel, hi, -⟩ | he
  · exact absurd hr (by simp [readsFlags, hi])
  · rw [hi]
    exact ⟨_, rfl⟩
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    rcases emitCore_cases hcore with ⟨d, src, hi, -⟩ | ⟨d, imm, hi, -⟩ | ⟨d, imm, hi, -⟩ |
      ⟨op, d, src, hi, -⟩ | ⟨c, cc, d, src, hi, -, -⟩ | ⟨d, src, hi, -⟩ | ⟨d, hi, -⟩ | ⟨d, hi, -⟩ |
      ⟨d, src, hi, -⟩ | ⟨d, hi, -⟩ | ⟨op, d, src, hi, -⟩ | ⟨d, src, hi, -⟩ | ⟨d, imm, hi, -⟩
    all_goals first
      | (rw [hi]; exact ⟨_, rfl⟩)
      | (rw [hi]; cases op <;> exact ⟨_, rfl⟩)
      | exact absurd hr (by simp [readsFlags, hi])

/-- **Flag transfer**: `flagOut` is sound. -/
theorem flags_out {i : Instr} {n : Nat} {code : List Silmaril.Wasm.Instr} (hc : emitX i n = some code)
    {σ σ' : State} {m m' : Silmaril.Process.Memory} (hx : exec i σ m n = .ok σ' m') {d : Bool}
    (ho : flagOut i d = true) (hd : d = true → Defined σ.flags) : Defined σ'.flags := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, -, -⟩ | ⟨rel, rfl, -⟩ | he
  · exact (emitX_shape hc hx).2.2 (hd ho)
  · exact (emitX_shape hc hx).2.2 (hd ho)
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    rcases emitCore_cases hcore with ⟨d', src, rfl, -⟩ | ⟨d', imm, rfl, -⟩ | ⟨d', imm, rfl, -⟩ |
      ⟨op, d', src, rfl, -⟩ | ⟨c, cc, d', src, rfl, -, -⟩ | ⟨d', src, rfl, -⟩ | ⟨d', rfl, -⟩ | ⟨d', rfl, -⟩ |
      ⟨d', src, rfl, -⟩ | ⟨d', rfl, -⟩ | ⟨op, d', src, rfl, -⟩ | ⟨d', src, rfl, -⟩ | ⟨d', imm, rfl, -⟩
    all_goals first
      | exact (emitX_shape hc hx).2.2 (hd ho)
      | (simp [exec, readRM, writeRM, retire, aluStep] at hx
         first
         | (obtain ⟨rfl, -⟩ := hx; simp [Defined, logicFlagsN, AluOp.flagsN])
         | (split at hx <;> simp at hx
            obtain ⟨rfl, -⟩ := hx
            rename_i h
            split at h <;> simp at h <;> obtain ⟨rfl, -⟩ := h <;> cases op <;>
              simp [Defined, logicFlagsN, AluOp.flagsN, addFlagsN, subFlagsN]))

/-- Jump targets at offsets. -/
theorem ofNat_tgt (b : Word) (o n : Nat) (rel : BitVec 8) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 n + rel.signExtend 64 =
      b + BitVec.ofNat 64 ((o + n + (rel.signExtend 64).toNat) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Fall-through at offsets. -/
theorem ofNat_ft (b : Word) (o n : Nat) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 n = b + BitVec.ofNat 64 (o + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- **Successors**: the next RIP is at one of `succs`. -/
theorem rip_succ {i : Instr} {n : Nat} {code : List Silmaril.Wasm.Instr} (hc : emitX i n = some code)
    {σ σ' : State} {m m' : Silmaril.Process.Memory} (hx : exec i σ m n = .ok σ' m') {b : Word} {o : Nat}
    (hrip : σ.rip = b + BitVec.ofNat 64 o) : ∃ o' ∈ succs o i n, σ'.rip = b + BitVec.ofNat 64 o' := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, -, -⟩ | ⟨rel, rfl, -⟩ | he
  · simp only [exec] at hx
    split at hx <;> simp at hx
    · obtain ⟨rfl, -⟩ := hx
      exact ⟨(o + n + (rel.signExtend 64).toNat) % 2 ^ 64, by simp [succs], by simp only [hrip, ofNat_tgt]⟩
    · obtain ⟨rfl, -⟩ := hx
      exact ⟨o + n, by simp [succs], by simp only [hrip, ofNat_ft]⟩
  · simp [exec] at hx
    obtain ⟨rfl, -⟩ := hx
    exact ⟨(o + n + (rel.signExtend 64).toNat) % 2 ^ 64, by simp [succs], by simp only [hrip, ofNat_tgt]⟩
  · have hr := (emit_rip he hx).1
    obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    refine ⟨o + n, ?_, by rw [hr, hrip, ofNat_ft]⟩
    rcases emitCore_cases hcore with ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨d, imm, rfl, -⟩ |
      ⟨op, d, src, rfl, -⟩ | ⟨c, cc, d, src, rfl, -, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨d, rfl, -⟩ |
      ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ <;>
      simp [succs]

/-- Offsets below `2^64` are injective. -/
theorem off_inj {b : Word} {x y : Nat} (h : b + BitVec.ofNat 64 x = b + BitVec.ofNat 64 y)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x = y := by
  have := congrArg BitVec.toNat (add_left_cancel h)
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- Lookups in a placed table. -/
theorem lookupI_place {b : Word} {rt : RTab} {w : Word} {i : Instr} {n : Nat}
    (h : lookupI (place b rt) w = some (i, n)) : ∃ o, (o, i, n) ∈ rt ∧ w = b + BitVec.ofNat 64 o := by
  have hm := lookupI_mem h
  simp only [place, List.mem_map] at hm
  obtain ⟨⟨o, i', n'⟩, he, heq⟩ := hm
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨o, he, rfl⟩

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **A Wasm ranking gives an x86 run** (termination) with the frame `tabWrites`, under the flag
dataflow check. The Wasm evaluation `exec` is a function, so the ranking's store is the one the
method's soundness (`emitX_sound`) produces. -/
theorem xrun_of_ranked {b : Word} {rt : RTab} {ann : List Nat} {entry : Nat}
    (hs : Supported (place b rt)) (hok : flagsOK rt ann entry = true) {f : Frame}
    {J : Nat → Store H → Prop} (hR : Ranked (compileTab (place b rt)) f J) (m : Silmaril.Process.Memory) :
    ∀ k s σ, J k s → Enc s f σ → FlagInv b ann σ →
      ∃ j σ', XRun (place b rt) m j σ σ' ∧ ∀ r, r ∉ tabWrites (place b rt) → σ'.read r = σ.read r := by
  simp only [flagsOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true] at hok
  obtain ⟨⟨⟨-, -⟩, hann⟩, htab⟩ := hok
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s σ hJ hE hinv
  cases hl : lookupI (place b rt) σ.rip with
  | none => exact ⟨0, σ, .done hl, fun _ _ => rfl⟩
  | some e =>
    show ∃ j σ', XRun (place b rt) m j σ σ' ∧ ∀ r, r ∉ tabWrites (place b rt) → σ'.read r = σ.read r
    obtain ⟨i, n⟩ := e
    obtain ⟨o, hmem, hro⟩ := lookupI_place hl
    obtain ⟨hread, hsucc⟩ := htab _ hmem
    have hlc := lookup_compile (w := σ.rip) hs
    rw [hl] at hlc
    obtain ⟨code, hlc, hcode⟩ := hlc
    obtain ⟨σ₁, hx⟩ : ∃ σ₁, exec i σ m n = .ok σ₁ m := by
      cases hrf : readsFlags i
      · exact progress_nf hcode hrf σ m
      · have ho : ann.contains o = true := by simpa [hrf] using hread
        exact emitX_progress hcode (hinv o (by simpa using ho) hro) m
    obtain ⟨-, s'', he'', hE₁, -⟩ := emitX_sound hcode hE hx
    obtain ⟨s', k', he', hJ', hlt⟩ := hR k s σ.rip code hJ hE.2.2.1 hlc
    rw [he''] at he'
    obtain rfl : s'' = s' := (Prod.mk.inj (Option.some.inj he')).1
    have hinv₁ : FlagInv b ann σ₁ := by
      intro o'' ho'' hr''
      obtain ⟨o', ho', hr'⟩ := rip_succ hcode hx hro
      obtain ⟨hlt', hflag⟩ := hsucc o' ho'
      obtain rfl : o' = o'' := off_inj (hr'.symm.trans hr'') hlt' (hann o'' ho'')
      have hfo : flagOut i (ann.contains o) = true := by
        simpa [List.contains_iff_mem, ho''] using hflag
      exact flags_out hcode hx hfo fun hd => hinv o (by simpa using hd) hro
    obtain ⟨j, σ', hrun, hfr⟩ := ih k' hlt s'' σ₁ hJ' hE₁ hinv₁
    refine ⟨j + 1, σ', .step hl hx hrun, fun r hr => ?_⟩
    rw [hfr r hr]
    refine frame_of_exec hcode hx r fun hw => hr ?_
    exact List.mem_flatMap.mpr ⟨_, lookupI_mem hl, hw⟩

/-- At the entry, the flag invariant holds vacuously. -/
theorem flagInv_entry {b : Word} {rt : RTab} {ann : List Nat} {entry : Nat}
    (hok : flagsOK rt ann entry = true) {σ : State} (hrip : σ.rip = b + BitVec.ofNat 64 entry) :
    FlagInv b ann σ := by
  simp only [flagsOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hne, hlt⟩, hann⟩, -⟩ := hok
  intro o ho hr
  obtain rfl := off_inj (hrip.symm.trans hr) hlt (hann o ho)
  simp [ho] at hne

open Silmaril.Sim.X86.G in
/-- **Table runs are machine runs** (the converse of `xrun_of_run`). -/
theorem run_of_xrun {tab : XTab} (hs : Supported tab) {mem : Silmaril.Process.Memory}
    (hcode : TabAt mem tab) (exit : Word) {k : Nat} {σ σ' : State} (h : XRun tab mem k σ σ') :
    Silmaril.Machine.Execution.run (stepOpt exit) k ⟨σ, mem⟩ = some ⟨σ', mem⟩ := by
  induction h with
  | done _ => rfl
  | @step σ σ₁ σ' i n k hl hx _ ih =>
    have hm := lookupI_mem hl
    have hf := hcode _ hm
    have hnr := emitX_ne_ret (hs _ hm)
    have hlen := fetch_length hf
    simp only at hf hlen
    rw [Silmaril.Machine.Execution.run_succ]
    have hst : stepOpt exit ⟨σ, mem⟩ = some ⟨σ₁, mem⟩ := by
      rw [stepOpt_eq_some_iff]
      simp only [step, hf]
      rw [hlen] at hx
      simp only [hx]
      split
      · rename_i h; exact absurd h.1 hnr
      · rfl
    rw [hst, Option.bind_some]
    exact ih

open Silmaril.Sim.X86.G in
/-- Consecutive non-empty spans of a loaded image, from offset `off`, are `BytesAt` there. -/
theorem bytesAt_of_loaded {mem : Silmaril.Process.Memory} {base : Word} {code : List (BitVec 8)}
    (h : Silmaril.X86.Ext.Loaded mem base code) : ∀ (bss : List (List (BitVec 8))) (off : Nat),
    (∀ bs ∈ bss, 0 < bs.length) → off + bss.flatten.length ≤ code.length →
    (code.drop off).take bss.flatten.length = bss.flatten →
    BytesAt mem (base + BitVec.ofNat 64 off) bss := by
  intro bss
  induction bss with
  | nil => intros; trivial
  | cons bs bss ih =>
    intro off hpos hfit hpre
    have hp := hpos bs List.mem_cons_self
    simp only [List.flatten_cons, List.length_append] at hfit hpre
    rw [List.take_add] at hpre
    obtain ⟨h₁, h₂⟩ := List.append_inj hpre (by simp; omega)
    refine ⟨?_, ?_⟩
    · rw [h.toNat_add (by omega), h.fetchBytes_sub hp (by omega), h₁]
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ih (off + bs.length) (fun b hb => hpos b (List.mem_cons_of_mem _ hb)) (by omega)
        (by rw [← List.drop_drop]; exact h₂)


end Silmaril.Sim.Reduce.Loop
