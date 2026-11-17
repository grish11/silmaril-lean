module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainStdin
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.ShaFini
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseStdout

/-! # GNU `sha256sum`: the end of the process after `main` returned 0

`task_exitPath` (proves `Task.exitPath`): the library takes `main`'s status to `exit (0)`,
which runs the exit handler `close_stdout` (`sha_closeStdout`: `stdout`'s buffer is flushed,
both streams closed without error), then the finalisers `__do_global_dtors_aux` (with
`__cxa_finalize`, nothing registered) and `_fini`, and halts with status 0 having written
everything `main` and `close_stdout` wrote.
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
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

set_option maxRecDepth 4000 in
theorem room_of_stack {W : World} {m : Memory} {sp : Word} (h : StackRoom W m sp) : Room W m sp 1024 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, h2, fun a ha hb => h3 a (by omega) hb⟩

set_option maxRecDepth 4000 in
theorem sha_in_k {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {n : Nat} (hn : n < 0xa188) {W : World}
    (hW : W.InImage = ShaImg b) : W.Kept (b + BitVec.ofNat 64 n).toNat :=
  Or.inl (by rw [hW]; exact sha_in hb hn)

set_option maxRecDepth 100000 in
/-- `completed.0` (`0xa040`) and its write permission are kept by the program's kept memory. -/
theorem bss_keep {W : World} {b : Word} (hW : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {m m' : Memory} (hk : Keeps W.Kept m m') (h : loadN m (b + 0xa040#64) 1 = some 0#64 ∧
      m.Permitted .write (b + 0xa040#64).toNat 1) :
    loadN m' (b + 0xa040#64) 1 = some 0#64 ∧ m'.Permitted .write (b + 0xa040#64).toNat 1 := by
  have e : (b + 0xa040#64).toNat = b.toNat + 0xa040 := addr_toNat (by omega)
  have hK : ∀ j < 1, W.Kept ((b + 0xa040#64).toNat + j) := fun j hj => by
    rw [e, World.Kept, hW]; exact Or.inl ⟨by omega, by omega⟩
  exact ⟨(loadN_keeps hk hK).trans h.1, (Keeps.permitted hk hK).2 h.2⟩

set_option maxRecDepth 100000 in
theorem loaded_keepK {W : World} {b : Word} (hW : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {m m' : Memory} (hk : Keeps W.Kept m m') (h : Loaded m (b + 0x6d44#64) shaFiniText) :
    Loaded m' (b + 0x6d44#64) shaFiniText := by
  have e : (b + 0x6d44#64).toNat = b.toNat + 0x6d44 := addr_toNat (by omega)
  unfold Loaded Memory.fetchBytes at h ⊢
  rw [hk.readWith (fun j hj => by
    rw [e, World.Kept, hW]; rw [sha_lens.2.2.1] at hj; exact Or.inl ⟨by omega, by omega⟩)]
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The end of the process, any status** (`Task.exitPathG`). -/
theorem task_exitPathG {E : Env} {W : World} {b lb : Word} : Task.exitPathG E W b lb := by
  intro XO s t X code Y hcode h
  have I := XO.cl.img
  have hb := XO.cl.hb
  have hgo : ¬ W.InImage W.gate.toNat := by rw [I]; exact XO.wo.gate_out
  obtain ⟨hj, hat, hd⟩ := h.ghost
  obtain ⟨st, hst, hste, hstr, hX⟩ := h.out
  -- `exit (0)`
  refine gate_exitRaxG hd (by rw [h.rip]; exact hgo) h.rip hj ?_ (hpend := XO.pend)
  intro t1 hAt1 hg1 hG1
  obtain ⟨hr1, hk1, -⟩ := hAt1
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd
  refine gate_exitG hd1 (by rw [hr1]; exact hgo) hr1 (by rw [hg1]) ?_
  intro t2 hAt2 hg2 hG2
  obtain ⟨hr2, hk2, -⟩ := hAt2
  have hd2 : t2.g.done = none := by rw [hg2]; exact hd1
  have hj2 : t2.g.jobs = [.call0 (b + 0x69b0#64), .call0 (b + 0x3ae0#64), .call0 (b + 0x6d44#64),
      .halt ((low32 (t.m.core.read .rax)).setWidth 64)] := by
    rw [hg2, hg1, exitJobs, XO.wo.finis]; simp [hat]
  -- `close_stdout`
  refine gate_call0G hd2 (by rw [hr2]; exact hgo) hr2 hj2 ?_
  intro t3 he3 hg3 hC3 hG3
  have hd3 : t3.g.done = none := by rw [hg3]; exact hd2
  have hk3 : Keeps W.Kept t.m.memory t3.m.memory := hk1.trans (hk2.trans he3.2.2.2.2.1)
  have hfile : ∀ f st', E.S.file t.m.memory f st' → E.S.file t3.m.memory f st' := fun f st' hf =>
    XO.atGate _ _ _ _ hG3 (XO.atGate _ _ _ _ hG2 (XO.atGate _ _ _ _ hG1 hf))
  refine sha_closeStdout XO.cl he3.1 (abiEntry_of he3.2.1 he3.2.2.1) (room_of_stack he3.2.2.2.1)
    (XO.atCall t3 hC3) hd3 (h.mem.2.keepW hb (imgW_img (skeepsImgW I hk3))) XO.rel (h.vars.keep hk3) XO.ne
    (hfile _ _ hst.1) hstr hste hst.2 (hfile _ _ h.err) rfl rfl rfl ?_
  intro t4 habi4 hk4 hout4 hj4 hat4 hd4 _ herr4
  have hr4 : t4.m.core.rip = W.gate := by rw [habi4.pc]; exact retOf_of he3.2.2.1
  have hk4' : Keeps W.Kept t.m.memory t4.m.memory := hk3.trans (hk4.mono fun a ha => Or.inl ha)
  -- `__do_global_dtors_aux`
  refine gate_call0G hd4 (by rw [hr4]; exact hgo) hr4 (by rw [hj4, hg3]) ?_
  intro t5 he5 hg5 _ _
  have hd5 : t5.g.done = none := by rw [hg5]; exact hd4
  have hk5 : Keeps W.Kept t.m.memory t5.m.memory := hk4'.trans he5.2.2.2.2.1
  refine sha_dtorsW I hb XO.wo.lz XO.cxa XO.cxa_out XO.gate_cxa XO.cxa_ne
    ⟨he5.1, he5.2.1, he5.2.2.1, he5.2.2.2.1, h.mem.1.keep hb (skeepsImgW I hk5), hd5⟩
    (bss_keep I hb hk5 h.bss).1 (bss_keep I hb hk5 h.bss).2 (by rw [hg5, hat4, hg3, hg2]) ?_
  intro u5 hru5 hgu5 hku5
  have hdu5 : u5.g.done = none := by rw [hgu5]; exact hd5
  have hlf : Loaded u5.m.memory (b + 0x6d44#64) shaFiniText := by
    have e : (b + 0x6d44#64).toNat = b.toNat + 0x6d44 := addr_toNat (by omega)
    have h0 := (h.mem.1.keep hb (skeepsImgW I hk5)).fini
    unfold Loaded Memory.fetchBytes at h0 ⊢
    rw [hku5.readWith (fun j hj => by
      rw [e, show (b + 0xa040#64).toNat = b.toNat + 0xa040 from addr_toNat (by omega)]
      rw [sha_lens.2.2.1] at hj
      exact ⟨⟨by omega, by omega⟩, by omega⟩)]
    exact h0
  -- `_fini`
  refine gate_call0G hdu5 (by rw [hru5]; exact hgo) hru5 (by rw [hgu5, hg5]) ?_
  intro t6 he6 hg6 _ _
  have hd6 : t6.g.done = none := by rw [hg6]; exact hdu5
  refine sha_finiW I hb he6.1 hd6 (loaded_keepK I hb he6.2.2.2.2.1 hlf) he6.2.2.1 ?_
  intro u6 hru6 hgu6 _
  have hdu6 : u6.g.done = none := by rw [hgu6]; exact hd6
  refine gate_halt hdu6 (by rw [hru6]; exact hgo) hru6 (by rw [hgu6, hg6, hgu5, hg5]) ?_
  intro t7 w hw1 hw2 hg7
  refine must_done ⟨⟨w, ?_, ?_⟩, ?_⟩
  · rw [hg7, h.rax]
    have e1 : code.toNat % 2 ^ 64 = code.toNat := Nat.mod_eq_of_lt (by have := code.isLt; omega)
    have e2 : code.toNat % 256 = code.toNat := Nat.mod_eq_of_lt hcode
    simp only [BitVec.toNat_setWidth, e1, e2]
  · rw [hw2 XO.rel, hgu6, hg6, hgu5, hg5, hout4, hg3, hg2, hg1]
    exact hX
  · rw [hg7]; simp only
    rw [hgu6, hg6, hgu5, hg5, herr4, hg3, hg2, hg1]; exact h.gerr

/-- **The end of the process** (`Task.exitPath`): the case `code = 0` of `task_exitPathG`. -/
theorem task_exitPath {E : Env} {W : World} {b lb : Word} : Task.exitPath E W b lb := by
  intro XO s t X h
  exact Silmaril.X86.RelIsa.Must.mono (fun _ h => h) (fun u hu => hu.1)
    (task_exitPathG XO s t X 0#32 t.g.err (by decide) h.toG)

end Silmaril.Elf.Link.Dyn.Sha256sum
