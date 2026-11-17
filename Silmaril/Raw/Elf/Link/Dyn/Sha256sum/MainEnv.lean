module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainPro
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseStdout

/-! # GNU `sha256sum`: the library state `main` relies on, and how it is kept

`MEnv … m`: the three standard streams in their states (`stdout`, `stderr`, `stdin` at `fi`), the
libc variables `stdout`/`stderr` (`StdVars`), and a set `C` of libc cells the program writes or
passes to the library (`program_invocation_name`, `optind`) together with the executable's image:
mapped and not library-private (`C` also writable).

It is kept by a push onto the stack (`MEnv.push`), by a program store outside the library's
private memory (`MEnv.store`, given the law `PrivKeep`), and by a library call returning with the
library frame `LibRet` and keeping every stream (`MEnv.lib`).

`PrivKeep E`: whether memory is library-private depends only on the private memory itself
(the law `StreamRep.priv_keep`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- The law `StreamRep.priv_keep`, as a proposition on `E` (kept so that statements can name it;
`privKeep` proves it). -/
def PrivKeep (E : Env) : Prop :=
  ∀ m m' : Memory, Keeps (E.S.priv m) m m' → E.S.priv m' = E.S.priv m

theorem privKeep (E : Env) : PrivKeep E := E.S.priv_keep

/-- `program_invocation_name` (libc `.data`). -/
def PinR (lb : Word) (a : Nat) : Prop := (lb + 0x205378#64).toNat ≤ a ∧ a < (lb + 0x205378#64).toNat + 8

/-- `optind`. -/
def OptR (E : Env) (a : Nat) : Prop := E.optindA.toNat ≤ a ∧ a < E.optindA.toNat + 4

/-- The libc variables `stderr` and `stdout`. -/
def VarR (lb : Word) (a : Nat) : Prop := (lb + 0x2056a0#64).toNat ≤ a ∧ a < (lb + 0x2056a0#64).toNat + 16

/-- **The library state `main` relies on.** -/
structure MEnv (E : Env) (W : World) (b lb : Word) (C : Nat → Prop) (fi : Word) (sto ste sti : St)
    (m : Memory) : Prop where
  out : E.S.file m E.stdoutF sto
  err : E.S.file m E.stderrF ste
  inp : E.S.file m fi sti
  vars : StdVars E W lb m
  np : ∀ a, ShaImg b a ∨ C a → ¬ E.S.priv m a ∧ m.permits .read a = true
  wr : ∀ a, C a → m.permits .write a = true

theorem StdVars.keepR {E : Env} {W : World} {lb : Word} {m m' : Memory} (h : StdVars E W lb m)
    (hk : Keeps (VarR lb) m m') : StdVars E W lb m' := by
  have e : (lb + 0x2056a8#64).toNat = (lb + 0x2056a0#64).toNat + 8 := by
    have := h.bound
    rw [show lb + 0x2056a8#64 = lb + 0x2056a0#64 + 8#64 by rw [BitVec.add_assoc]; rfl, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by rw [show (8#64).toNat = 8 from rfl]; omega)]
    rfl
  refine ⟨?_, ?_, h.kept, h.bound⟩
  · rw [loadN_keeps hk (fun k hk => by rw [e]; simp only [VarR]; omega)]; exact h.out
  · rw [loadN_keeps hk (fun k hk => by simp only [VarR]; omega)]; exact h.err

theorem MEnv.mono {E : Env} {W : World} {b lb : Word} {C C' : Nat → Prop} {fi : Word} {sto ste sti : St}
    {m : Memory} (h : MEnv E W b lb C fi sto ste sti m) (hC : ∀ a, C' a → C a) :
    MEnv E W b lb C' fi sto ste sti m :=
  ⟨h.out, h.err, h.inp, h.vars, fun a ha => h.np a (ha.imp id (hC a)), fun a ha => h.wr a (hC a ha)⟩

/-- A push at `sp` (onto the stack, above the streams, outside the kept memory and `C`). -/
theorem MEnv.push {E : Env} {W : World} {b lb : Word} {C : Nat → Prop} {fi : Word} {sto ste sti : St}
    {m : Memory} (h : MEnv E W b lb C fi sto ste sti m) {sp v : Word} (hlo : E.S.lo ≤ (sp - 8#64).toNat)
    (hk : ∀ a, (sp - 8#64).toNat ≤ a → a < (sp - 8#64).toNat + 8 → ¬ W.Kept a ∧ ¬ C a) :
    MEnv E W b lb C fi sto ste sti (pushMem m sp v) := by
  have hp : E.S.priv (pushMem m sp v) = E.S.priv m :=
    E.S.priv_local _ _ fun a ha => ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (fun x hx => by omega) a ha).1,
      fun acc => rfl⟩
  refine ⟨file_push h.out hlo, file_push h.err hlo, file_push h.inp hlo, h.vars.keep (pushMem_keeps fun x hx => by
    by_contra hc; exact (hk x (by omega) (by omega)).1 hx), fun a ha => ?_, fun a ha => ?_⟩
  · rw [hp]; exact h.np a ha
  · exact h.wr a ha

/-- A program store of `k` bytes at `a`, outside the library's private memory and `stdout`/`stderr`. -/
theorem MEnv.store {E : Env} {W : World} {b lb : Word} {C : Nat → Prop} {fi : Word} {sto ste sti : St}
    {m : Memory} (h : MEnv E W b lb C fi sto ste sti m) (hpk : PrivKeep E) {a v : Word} {k : Nat}
    (hnp : ∀ x, a.toNat ≤ x → x < a.toNat + k → ¬ E.S.priv m x ∧ ¬ VarR lb x) :
    MEnv E W b lb C fi sto ste sti (storeMem m a k v) := by
  have hkp : Keeps (E.S.priv m) m (storeMem m a k v) := storeMem_keeps fun x hx => by
    by_contra hc; exact (hnp x (by omega) (by omega)).1 hx
  have hp : E.S.priv (storeMem m a k v) = E.S.priv m := hpk _ _ hkp
  have hf : ∀ f st, E.S.file m f st → E.S.file (storeMem m a k v) f st := fun f st hf =>
    (E.S.local_ _ _ _ _ (hkp.mono fun x hx => E.S.foot_priv _ _ _ _ hf hx) hf).1
  refine ⟨hf _ _ h.out, hf _ _ h.err, hf _ _ h.inp, h.vars.keepR (storeMem_keeps fun x hx => by
    by_contra hc; exact (hnp x (by omega) (by omega)).2 hx), fun x hx => ?_, fun x hx => ?_⟩
  · rw [hp]; exact h.np x hx
  · exact h.wr x hx

/-- A library call from `e` returning at `t` with the library frame (writing `fp`, outside the
kept memory and `C`) and keeping every stream. -/
theorem MEnv.lib {E : Env} {W : World} {b lb : Word} {C : Nat → Prop} {fi : Word} {sto ste sti : St}
    (I : W.InImage = ShaImg b) {e t : PState} (h : MEnv E W b lb C fi sto ste sti e.m.memory)
    {fp : Nat → Prop} (hl : LibRet E W fp e t) (ho : OthersKept E e t [])
    (hfp : ∀ a, fp a → ¬ W.Kept a ∧ ¬ C a) : MEnv E W b lb C fi sto ste sti t.m.memory := by
  obtain ⟨⟨-, hk⟩, -, -, hk2, hpr, -⟩ := hl
  have hkk : Keeps W.Kept e.m.memory t.m.memory :=
    hk.mono fun x hx => ⟨Or.inl hx, fun hf => (hfp x hf).1 hx⟩
  have himg : ∀ x, ShaImg b x → W.Kept x := fun x hx => Or.inl (by rw [I]; exact hx)
  refine ⟨ho _ _ (by simp) h.out, ho _ _ (by simp) h.err, ho _ _ (by simp) h.inp, h.vars.keep hkk,
    fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := h.np a ha
    have hnf : ¬ fp a := fun hf => by
      rcases ha with ha | ha
      · exact (hfp a hf).1 (himg a ha)
      · exact (hfp a hf).2 ha
    refine ⟨fun hp => ?_, by rw [(hk2 a ⟨h1, hnf, h2⟩).2]; exact h2⟩
    rcases hpr a hp with hp' | hp'
    · exact h1 hp'
    · rw [h2] at hp'; cases hp'
  · obtain ⟨h1, h2⟩ := h.np a (Or.inr ha)
    rw [(hk2 a ⟨h1, fun hf => (hfp a hf).2 ha, h2⟩).2]; exact h.wr a ha

end Silmaril.Elf.Link.Dyn.Sha256sum
