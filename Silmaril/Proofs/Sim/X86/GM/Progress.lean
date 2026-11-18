module

public import Silmaril.Proofs.Sim.X86.GM.Form
public import Silmaril.Sim.X86.Loop.Thms

/-!
# GM: the window check, progress and flag definedness

* **`emitM_holds`**: a method that evaluates made its access inside the window (the check
  passed): the Wasm side establishes the separation side condition of `emitM_sound`;
* **`emitM_progress`**: from a state with defined modelled flags whose access lies in the window
  (of a memory `MemEnc` describes), every instruction with a method retires, and the flags stay
  defined.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State AluOp)
open Silmaril.X86.Ext (Sz RM Mem Base Index Result retire readRM writeRM aluStep)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

theorem accessMem_emitX {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitX i len = some code) (σ : State) : accessMem i σ len = none := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, -, -⟩ | ⟨rel, rfl, -⟩ | he
  · rfl
  · rfl
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    rcases emitCore_cases hcore with
      ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ |
      ⟨c, cc, d, src, rfl, -, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨d, rfl, -⟩ |
      ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ <;> rfl

theorem access_emitX {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitX i len = some code) (σ : State) : access i σ len = none := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, -, -⟩ | ⟨rel, rfl, -⟩ | he
  · rfl
  · rfl
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    rcases emitCore_cases hcore with
      ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨d, imm, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ |
      ⟨c, cc, d, src, rfl, -, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨d, rfl, -⟩ |
      ⟨d, src, rfl, -⟩ | ⟨d, rfl, -⟩ | ⟨op, d, src, rfl, -⟩ | ⟨d, src, rfl, -⟩ | ⟨d, imm, rfl, -⟩ <;>
      first | rfl | (cases op <;> rfl)

theorem access_mem {i : Silmaril.X86.Ext.Instr} {σ : State} {len : Nat} {a : Word}
    (h : accessMem i σ len = some a) : access i σ len = some (a, 8) := by
  simp only [access, h]

/-! ## The check passed, one form at a time -/

section
variable {W : Win} {len : Nat} {c : List Instr} {r : Store H × Frame × List Val}

theorem emitMem_holds_load {sz : Sz} {d : Reg} {m : Mem} (hmem : loadM W sz d m len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem (.load sz d m) σ len = some a → W.Holds a := by
  obtain ⟨⟨rfl, hp⟩, rfl⟩ := some_of_ite hmem
  intro a ha
  have hax : m.addr σ (σ.rip + BitVec.ofNat 64 len) = a := Option.some.inj ha
  obtain ⟨r₁, hr₁⟩ := exec_append_some he
  obtain ⟨r', hr'⟩ := exec_append_some hr₁
  exact hax ▸ load_holds (pure_addr hE hp _) h32 hlim hr'

theorem emitMem_holds_store {sz : Sz} {dst : RM} {src : Reg}
    (hmem : storeM W sz dst src len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem (.mov sz dst src) σ len = some a → W.Holds a := by
  obtain ⟨m, rfl, rfl, -, hp, rfl⟩ := storeM_some hmem
  intro a ha
  have hax : m.addr σ (σ.rip + BitVec.ofNat 64 len) = a := Option.some.inj ha
  obtain ⟨r', hr'⟩ := exec_append_some he
  exact hax ▸ store_holds (pure_addr hE hp _) h32 hlim hr'

theorem emitMem_holds_push {x : Reg} (hmem : emitMem W (.push x) len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem (.push x) σ len = some a → W.Holds a := by
  obtain ⟨-, rfl⟩ := some_of_ite hmem
  intro a ha
  have hax : σ.read .rsp - 8#64 = a := Option.some.inj ha
  obtain ⟨r₁, hr₁⟩ := exec_append_some he
  obtain ⟨r₂, hr₂⟩ := exec_append_some hr₁
  obtain ⟨r', hr'⟩ := exec_append_some hr₂
  exact hax ▸ store_holds (pure_rspDown hE) h32 hlim hr'

theorem emitMem_holds_pop {x : Reg} (hmem : emitMem W (.pop x) len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem (.pop x) σ len = some a → W.Holds a := by
  obtain rfl := (Option.some.inj hmem).symm
  intro a ha
  have hax : σ.read .rsp = a := Option.some.inj ha
  obtain ⟨r₁, hr₁⟩ := exec_append_some he
  obtain ⟨r', hr'⟩ := exec_append_some hr₁
  exact hax ▸ load_holds (pure_gget (hE.2.1 .rsp)) h32 hlim hr'

theorem emitMem_holds_call {rel : BitVec 32} (hmem : emitMem W (.call rel) len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem (.call rel) σ len = some a → W.Holds a := by
  obtain ⟨-, rfl⟩ := some_of_ite hmem
  intro a ha
  have hax : σ.read .rsp - 8#64 = a := Option.some.inj ha
  obtain ⟨r₁, hr₁⟩ := exec_append_some he
  obtain ⟨r', hr'⟩ := exec_append_some hr₁
  exact hax ▸ store_holds (pure_rspDown hE) h32 hlim hr'

theorem emitMem_holds_ret (hmem : emitMem W .ret len = some c)
    (hE : Enc s f σ) (h32 : W.size ≤ 2 ^ 32) (hlim : W.lo.toNat + W.size ≤ 2 ^ 64)
    (he : exec s f [] c = some r) : ∀ a, accessMem .ret σ len = some a → W.Holds a := by
  obtain rfl := (Option.some.inj hmem).symm
  intro a ha
  have hax : σ.read .rsp = a := Option.some.inj ha
  obtain ⟨r', hr'⟩ := exec_append_some he
  exact hax ▸ load_holds (pure_gget (hE.2.1 .rsp)) h32 hlim hr'

end

/-- The check passed (memory and stack forms). -/
theorem emitMem_holds {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {c : List Instr}
    (hmem : emitMem W i len = some c) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {r : Store H × Frame × List Val} (he : exec s f [] c = some r) :
    ∀ a, accessMem i σ len = some a → W.Holds a := by
  obtain ⟨B, -, -, h32, hlim, -⟩ := id hM
  cases i with
  | load sz d m => exact emitMem_holds_load hmem hE h32 hlim he
  | mov sz dst src => exact emitMem_holds_store hmem hE h32 hlim he
  | push x => exact emitMem_holds_push hmem hE h32 hlim he
  | pop x => exact emitMem_holds_pop hmem hE h32 hlim he
  | call rel => exact emitMem_holds_call hmem hE h32 hlim he
  | ret => exact emitMem_holds_ret hmem hE h32 hlim he
  | _ => exact fun _ ha => nomatch ha

/-! ## Progress, one form at a time -/

section
variable {W : Win} {len : Nat} {c : List Instr} {mem : Silmaril.Process.Memory}

theorem emitMem_progress_load {sz : Sz} {d : Reg} {m : Mem} (hmem : loadM W sz d m len = some c)
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a, accessMem (.load sz d m) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.load sz d m) σ mem len = .ok σ' mem' ∧
      Defined σ'.flags := by
  obtain ⟨⟨rfl, -⟩, -⟩ := some_of_ite hmem
  obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
  refine ⟨{ Sz.q.write σ d (v.setWidth Sz.q.bits) with rip := σ.rip + BitVec.ofNat 64 len },
    mem, ?_, hd⟩
  simp only [Silmaril.X86.Ext.exec, readRM, show Sz.q.bytes = 8 from rfl, hv, Option.map_some,
    retire]

theorem emitMem_progress_store {sz : Sz} {dst : RM} {src : Reg}
    (hmem : storeM W sz dst src len = some c) (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a, accessMem (.mov sz dst src) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.mov sz dst src) σ mem len = .ok σ' mem' ∧
      Defined σ'.flags := by
  obtain ⟨m, rfl, rfl, hrw, -, -⟩ := storeM_some hmem
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hrw (hw _ rfl) (σ.read src)
  have hsrc : @BitVec.setWidth Sz.q.bits 64 (σ.read src) = σ.read src := BitVec.setWidth_eq _
  refine ⟨{ σ with rip := σ.rip + BitVec.ofNat 64 len }, mem', ?_, hd⟩
  simp only [Silmaril.X86.Ext.exec, writeRM, Sz.read_q, show Sz.q.bytes = 8 from rfl]
  rw [hsrc, hst]
  rfl

theorem emitMem_progress_push {x : Reg} (hmem : emitMem W (.push x) len = some c)
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a, accessMem (.push x) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.push x) σ mem len = .ok σ' mem' ∧ Defined σ'.flags := by
  obtain ⟨hrw, -⟩ := some_of_ite hmem
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hrw (hw _ rfl) (σ.read x)
  refine ⟨{ σ.write .rsp (σ.read .rsp - 8#64) with rip := σ.rip + BitVec.ofNat 64 len }, mem', ?_,
    hd⟩
  simp only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some, retire]

theorem emitMem_progress_call {rel : BitVec 32} (hmem : emitMem W (.call rel) len = some c)
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a, accessMem (.call rel) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.call rel) σ mem len = .ok σ' mem' ∧ Defined σ'.flags := by
  obtain ⟨hrw, -⟩ := some_of_ite hmem
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hrw (hw _ rfl) (σ.rip + BitVec.ofNat 64 len)
  refine ⟨{ σ.write .rsp (σ.read .rsp - 8#64) with
    rip := σ.rip + BitVec.ofNat 64 len + rel.signExtend 64 }, mem', ?_, hd⟩
  simp only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some]

theorem emitMem_progress_aluI {sz : Sz} {op : AluOp} {dst : RM} {n : Nat} {imm : BitVec n}
    (hmem : aluIM sz op dst (imm.signExtend 64) len = some c) :
    ∃ σ' mem', retire (σ.rip + BitVec.ofNat 64 len) (aluStep sz op dst (imm.signExtend sz.bits)
      σ mem (σ.rip + BitVec.ofNat 64 len)) = .ok σ' mem' ∧ Defined σ'.flags := by
  obtain ⟨d, rfl, rfl, -⟩ := aluIM_some hmem
  cases op <;> exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩

end

/-- Progress (memory and stack forms). -/
theorem emitMem_progress {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {c : List Instr}
    (hmem : emitMem W i len = some c) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a, accessMem i σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem' ∧ Defined σ'.flags := by
  cases i with
  | load sz d m => exact emitMem_progress_load hmem hM hd hw
  | mov sz dst src => exact emitMem_progress_store hmem hM hd hw
  | push x => exact emitMem_progress_push hmem hM hd hw
  | pop x =>
    obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
    refine ⟨{ (σ.write .rsp (σ.read .rsp + 8#64)).write x v with
      rip := σ.rip + BitVec.ofNat 64 len }, mem, ?_, hd⟩
    simp only [Silmaril.X86.Ext.exec, popWord_loadN hv, Option.map_some, retire]
  | call rel => exact emitMem_progress_call hmem hM hd hw
  | ret =>
    obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
    refine ⟨{ σ.write .rsp (σ.read .rsp + 8#64) with rip := v }, mem, ?_, hd⟩
    simp only [Silmaril.X86.Ext.exec, popWord_loadN hv]
  | aluI8 sz op dst imm => exact emitMem_progress_aluI hmem
  | aluI sz op dst imm => exact emitMem_progress_aluI hmem
  | _ => cases hmem

/-! ## All methods with memory -/

/-- The immediate ALU forms with a method have no access. -/
theorem access_aluIM {sz : Sz} {op : AluOp} {dst : RM} {k : Word} {len : Nat}
    {c : List Instr} (hmem : aluIM sz op dst k len = some c) :
    (cmpIOf sz op dst k).bind (·.access σ (σ.rip + BitVec.ofNat 64 len)) = none := by
  obtain ⟨d, rfl, rfl, -⟩ := aluIM_some hmem
  simp only [cmpIOf, flagOf, opdOf]
  split <;> rfl

set_option linter.unusedTactic false in
/-- The memory and stack forms without an 8-byte access have no access. -/
theorem access_emitMem {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {c : List Instr}
    (hmem : emitMem W i len = some c) (h : accessMem i σ len = none) : access i σ len = none := by
  simp only [access, h]
  cases i with
  | load sz d m =>
    obtain ⟨⟨rfl, -⟩, -⟩ := some_of_ite hmem
    exact absurd h (by simp [accessMem])
  | aluI8 sz op dst imm => exact access_aluIM hmem
  | aluI sz op dst imm => exact access_aluIM hmem
  | _ => first | (cases hmem; done) | (cases h; done) | rfl

/-- **Soundness of the methods with memory**: if the store encodes `σ` (`Enc`) and the window
of `mem` (`MemEnc`), the instruction's memory access (if any) lies in the window, and
`Ext.exec i σ mem len` retires with `σ'`, `mem'`, then the method evaluates to a store encoding
`σ'` and the window of `mem'`, and `mem'` differs from `mem` only inside the window. -/
theorem emitM_sound {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitM W i len = some code) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {σ' : State} {mem' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem')
    (hw : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ MemEnc s' f mem' W ∧
      mem.WritesWithin mem' W.Mem := by
  cases hmem : emitMem W i len with
  | some c =>
    simp only [emitM, hmem, Option.some.injEq] at hc
    subst hc
    exact emitMem_sound hmem hE hM hx fun a h => hw a 8 (access_mem h)
  | none =>
  cases hX : emitX i len with
  | some c =>
    simp only [emitM, hmem, hX, Option.some.injEq] at hc
    subst hc
    obtain ⟨rfl, -, -⟩ := emitX_shape hX hx
    obtain ⟨-, s', he, hE', hF⟩ := emitX_sound hX hE hx
    refine ⟨s', he, hE', hM.congr ?_, Silmaril.Process.Memory.WritesWithin.refl _ _⟩
    rw [hF.2.1]
    simp [wbytes, Store.mem?]
  | none =>
    simp only [emitM, hmem, hX] at hc
    exact emitForm_sound hc hE hM hx hw

/-- **The check passed**: a method that evaluates made its access inside the window. -/
theorem emitM_holds {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitM W i len = some code) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {r : Store H × Frame × List Val} (he : exec s f [] code = some r) :
    ∀ a k, access i σ len = some (a, k) → W.HoldsK k a := by
  cases hmem : emitMem W i len with
  | some c =>
    show ∀ a k, access i σ len = some (a, k) → W.HoldsK k a
    have hcode : c = code := by simpa only [emitM, hmem, Option.some.injEq] using hc
    intro a k ha
    cases h : accessMem i σ len with
    | none => exact nomatch (access_emitMem hmem h).symm.trans ha
    | some a' =>
      obtain ⟨rfl, rfl⟩ : a' = a ∧ 8 = k :=
        Prod.mk.inj (Option.some.inj ((access_mem h).symm.trans ha))
      exact emitMem_holds hmem hE hM (hcode ▸ he) _ h
  | none =>
  cases hX : emitX i len with
  | some c =>
    intro a k ha
    exact nomatch (access_emitX hX σ).symm.trans ha
  | none =>
    have hf : emitForm W i len = some code := by simpa only [emitM, hmem, hX] using hc
    exact emitForm_holds hf hE hM he

/-- **Progress with memory**: with defined modelled flags and the access in the window, every
instruction with a method retires, keeping the flags defined. -/
theorem emitM_progress {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitM W i len = some code) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem' ∧ Defined σ'.flags := by
  cases hmem : emitMem W i len with
  | some c => exact emitMem_progress hmem hM hd fun a h => hw a 8 (access_mem h)
  | none =>
  cases hX : emitX i len with
  | some c =>
    obtain ⟨σ', hx⟩ := emitX_progress hX hd mem
    exact ⟨σ', mem, hx, (emitX_shape hX hx).2.2 hd⟩
  | none =>
    simp only [emitM, hmem, hX] at hc
    exact emitForm_progress hc hM hd hw

end Silmaril.Sim.X86.GM
