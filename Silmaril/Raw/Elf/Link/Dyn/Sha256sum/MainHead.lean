module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainLocale

/-! # GNU `sha256sum`: `main` from its entry to `0x2820`

`sha_main_head` chains the prologue (`sha_main_pro`), `set_program_name` (`sha_main_spn`) and
the locale set-up (`sha_main_locale`), from `main`'s entry state with the library state `MEnv`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- `MEnv` is kept when the memory below the streams, the kept memory and `C` are. -/
theorem MEnv.keepLow {E : Env} {W : World} {b lb : Word} {C : Nat → Prop} {fi : Word} {sto ste sti : St}
    (I : W.InImage = ShaImg b) {m m' : Memory} (h : MEnv E W b lb C fi sto ste sti m)
    (hk : Keeps (fun a => a < E.S.lo ∨ W.Kept a ∨ C a) m m') : MEnv E W b lb C fi sto ste sti m' := by
  have hp : E.S.priv m' = E.S.priv m := E.S.priv_local _ _ fun a ha => hk a (Or.inl ha)
  have hf : ∀ f st, E.S.file m f st → E.S.file m' f st := fun f st hf =>
    (E.S.local_ _ _ _ _ (hk.mono fun x hx => Or.inl (E.S.foot_lo _ _ _ _ hf hx)) hf).1
  have hP : ∀ a, ShaImg b a ∨ C a → a < E.S.lo ∨ W.Kept a ∨ C a := fun a ha =>
    ha.elim (fun h => Or.inr (Or.inl (Or.inl (by rw [I]; exact h)))) (fun h => Or.inr (Or.inr h))
  refine ⟨hf _ _ h.out, hf _ _ h.err, hf _ _ h.inp, h.vars.keep (hk.mono fun x hx => Or.inr (Or.inl hx)),
    fun a ha => ?_, fun a ha => ?_⟩
  · rw [hp, (hk a (hP a ha)).2]; exact h.np a ha
  · rw [(hk a (Or.inr (Or.inr ha))).2]; exact h.wr a ha

set_option maxRecDepth 100000 in
/-- **`main` from its entry (`0x2750`) to `0x2820`**, for a program name `argv[0]` without `/`. -/
theorem sha_main_headP {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hsr : ImpOk W sr (nm "strrchr") (strrchrStep E W)) (L : LocImps E W lb) (hpk : PrivKeep E)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s : PState}
    (hrip : s.m.core.rip = b + 0x2750#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 4096) (hd : s.g.done = none)
    (hm : ShaMemAll b lb kb sr sc s.m.memory) (hrw : ShaRw b s.m.memory)
    (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (henv : MEnv E W b lb C fi sto ste sti s.m.memory)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hpinC : ∀ a, PinR lb a → C a) (hpinK : ∀ a, PinR lb a → ¬ W.Kept a)
    (hlb : lb.toNat + 0x2056b0 < 2 ^ 64) (hImgVar : ∀ a, ShaImg b a → ¬ VarR lb a)
    (hArgsImg : ∀ a, W.args a → ¬ ShaImg b a)
    {a0p : Word} {a0 : List Byte}
    (hargv : loadN s.m.memory (s.m.core.read .rsi) 8 = some a0p)
    (hak : ∀ k, k < 8 → W.Kept ((s.m.core.read .rsi).toNat + k))
    (ha0 : CStr s.m.memory a0p a0) (ha0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j))
    (hnz : a0p ≠ 0#64) (hslash : ∀ x ∈ a0, x ≠ 0x2f#8)
    {g : Word} (hg : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ s1 x, MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g →
      loadN x.m.memory (lb + 0x205378#64) 8 = some a0p → MustQ W Q x) : MustQ W Q s := by
  have hal := habi.aligned
  have hsp := hroom.1
  refine sha_main_pro I hb hrip hroom hd hm ?_
  intro u hP
  have henvU : MEnv E W b lb C fi sto ste sti u.m.memory := by
    refine henv.keepLow I fun a ha => ⟨hP.low a ?_, fun acc => by simp only [Memory.permits, hP.regs]⟩
    rcases ha with ha | ha | ha
    · left; omega
    · by_contra hc
      exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
    · have := hC a ha; omega
  refine sha_main_spn I hb hlz hsr hpk hP hal hlo henvU hC hargv hak ha0 ha0k hnz hslash hg hgk ?_
  intro v hS
  have hrwV : ShaRw b v.m.memory := by
    intro j hj
    have hi : W.Kept (b.toNat + 0xa160 + j) := Or.inl (by rw [I]; exact ⟨by omega, by omega⟩)
    rw [(hS.body.keep _ (Or.inl hi)).2, (hS.body.keep _ (Or.inl hi)).2]
    exact hrw j hj
  exact sha_main_localeP I hb hlz L hpk hS hrwV hal hlo hC hpinC hpinK hlb hImgVar hArgsImg k

set_option maxRecDepth 100000 in
/-- **`main` from its entry (`0x2750`) to `0x2820`**, for a program name `argv[0]` without `/`. -/
theorem sha_main_head {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hsr : ImpOk W sr (nm "strrchr") (strrchrStep E W)) (L : LocImps E W lb) (hpk : PrivKeep E)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s : PState}
    (hrip : s.m.core.rip = b + 0x2750#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 4096) (hd : s.g.done = none)
    (hm : ShaMemAll b lb kb sr sc s.m.memory) (hrw : ShaRw b s.m.memory)
    (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (henv : MEnv E W b lb C fi sto ste sti s.m.memory)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hpinC : ∀ a, PinR lb a → C a) (hpinK : ∀ a, PinR lb a → ¬ W.Kept a)
    (hlb : lb.toNat + 0x2056b0 < 2 ^ 64) (hImgVar : ∀ a, ShaImg b a → ¬ VarR lb a)
    (hArgsImg : ∀ a, W.args a → ¬ ShaImg b a)
    {a0p : Word} {a0 : List Byte}
    (hargv : loadN s.m.memory (s.m.core.read .rsi) 8 = some a0p)
    (hak : ∀ k, k < 8 → W.Kept ((s.m.core.read .rsi).toNat + k))
    (ha0 : CStr s.m.memory a0p a0) (ha0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j))
    (hnz : a0p ≠ 0#64) (hslash : ∀ x ∈ a0, x ≠ 0x2f#8)
    {g : Word} (hg : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ s1 x, MainLoc E W b lb kb sr sc C fi sto ste sti s s1 x g → MustQ W Q x) : MustQ W Q s :=
  sha_main_headP I hb hlz hsr L hpk hrip habi hroom hd hm hrw hlo henv hC hpinC hpinK hlb hImgVar hArgsImg
    hargv hak ha0 ha0k hnz hslash hg hgk fun s1 x h _ => k s1 x h

end Silmaril.Elf.Link.Dyn.Sha256sum
