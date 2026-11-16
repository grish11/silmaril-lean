module

public import Silmaril.Proofs.Sim.RV64.Reduce.Sound

/-!
# Specialising `step` to a known instruction word

`step_sound` is proved once for the whole fetch-decode-dispatch body. Here it is turned into a
**partial evaluator** for triples about `step`: a triple `tripleSpec … Pre Post` holds as soon
as `Post` follows from the *specialised semantics* `StepPost` of the call (exactly one reference
step on the abstraction, frame outside the register block). For a known word `w`
(`fetched_word`), the reference step is `Silmaril.RiscV.step i` with `decode w = some i`
computed by evaluation, so a per-instruction Wasm triple reduces to arithmetic on the registers
(`retire_of_word`, `regs_after`) and never unfolds the simulator's 21-way dispatch.

* `triple_of_stepPost`: the generic rule;
* `retire_of_word`: a call from memory whose fetched word decodes to `i` retires `step i`;
* `absState_regs`, `absState_pc`, `ld64_after`, `ld32_after`: reading registers, `pc` and code
  bytes before and after a retired call.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Reduce

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Words (MemAt SameOutside)
open Silmaril.Wasm.Logic.Hoare (TSafe TFSpecAt FSpecValid)
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt)
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Triples about `step` from its specialised semantics.** -/
theorem triple_of_stepPost {fi : FuncInst H} {a ma : Nat} {mt : MemoryType}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) {Pre : ByteArray → Prop} {Post : BitVec 32 → ByteArray → Prop}
    (hwf : ∀ B, Pre B → WF B) (hpost : ∀ B st B', Pre B → StepPost B st B' → Post st B') :
    FSpecValid P host a (tripleSpec fi a ma mt Pre Post) := by
  intro n s args hpre f vs₀ c hc
  obtain ⟨hf, rfl, B, hm, hp⟩ := hpre
  have hT := step_sound (P := P) (host := host) (a := a) (ma := ma) (mt := mt) (B := B) hcode he
    hps hrs s [] ⟨hf, rfl, hm, hwf B hp⟩ f vs₀ c hc
  refine (TSafe.safe hT n).post_mono fun s' f' o h => ?_
  obtain ⟨hf', h⟩ := h
  refine ⟨hf', ?_⟩
  rcases h with ⟨res, ho, st, B', hr, rfl, hsp⟩ | ⟨ho, h⟩ | ⟨e, ho, h⟩
  · exact .inl ⟨res, ho, st, B', hr, hm.setMem B', hpost B st B' hp hsp⟩
  · obtain ⟨_, _, h, -⟩ := h; cases h
  · obtain ⟨_, _, h, -⟩ := h; cases h

/-- The fetched word decodes to `i`: a call retires exactly `Silmaril.RiscV.step i`. -/
theorem retire_of_word {B B' : ByteArray} {st : BitVec 32} {w : BitVec 32}
    {i : Silmaril.RiscV.Instr} (hw : absCode B (ld64 B 0) = some w)
    (hd : Silmaril.RiscV.decode w = some i) (h : StepPost B st B') :
    st = 0 ∧ absState B' = Silmaril.RiscV.step i (absState B) ∧ SameOutside B B' 0 256 := by
  have hr : refStep (absCode B) (absState B) = some (Silmaril.RiscV.step i (absState B)) := by
    simp only [refStep, show (absState B).pc = ld64 B 0 from rfl, hw, hd, Option.bind_some,
      Option.map_some]
  rcases h with ⟨h0, hs, hso⟩ | ⟨-, -, hn⟩
  · rw [hr] at hs
    exact ⟨h0, (Option.some.inj hs).symm, hso⟩
  · rw [hr] at hn; cases hn

theorem absState_regs (B : ByteArray) (r : Silmaril.RiscV.Reg) (hr : r ≠ 0#5) :
    (absState B).regs r = ld64 B (8 * r.toNat) := by simp [absState, hr]

theorem absState_pc (B : ByteArray) : (absState B).pc = ld64 B 0 := rfl

/-- Bytes outside the register block are unchanged by a retired call. -/
theorem ld64_after {B B' : ByteArray} (h : SameOutside B B' 0 256) (a : Nat) (ha : 256 ≤ a) :
    ld64 B' a = ld64 B a := by
  simp only [ld64, bytesAt_of_sameOutside h ⟨a, 8⟩ ha]

theorem ld32_after {B B' : ByteArray} (h : SameOutside B B' 0 256) (a : Nat) (ha : 256 ≤ a) :
    ld32 B' a = ld32 B a := by
  simp only [ld32, bytesAt_of_sameOutside h ⟨a, 4⟩ ha]

/-- The fetched word, from the `pc`, `code_end` and code bytes. -/
theorem fetched_word {B : ByteArray} {pc en : Nat} {w : BitVec 32}
    (hpc : ld64 B 0 = BitVec.ofNat 64 pc) (hen : ld64 B 264 = BitVec.ofNat 64 en)
    (hw : ld32 B pc = w) (h4 : pc % 4 = 0) (h1 : 4096 ≤ pc) (h2 : pc + 4 ≤ en)
    (h3 : en ≤ 65536) : absCode B (ld64 B 0) = some w := by
  have hp : (ld64 B 0).toNat = pc := by rw [hpc, BitVec.toNat_ofNat]; omega
  have hc : codeEnd B = en := by simp only [codeEnd, hen, BitVec.toNat_ofNat]; omega
  simp only [absCode, hp, hc, hw]
  rw [ite_eq_left ⟨h4, h1, h2, h3⟩]

end Silmaril.Sim.RV64.Reduce
