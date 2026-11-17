module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiMid
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainStdin

/-! # GNU `sha256sum FILE…`: the operand loop's invariant, and one operand

`main`'s operand loop (`0x2b57`–`0x2c91`) on the success tier: each operand is a readable file
whose name is printed verbatim. The invariant is stated at two points of an iteration:

* `LoopFr … ip q p n rest X g`: `main`'s frame (a FRESH body: base = `main`'s entry registers
  with the current memory), the loop's registers (`r12 = p` the current name, `r15 = q` its
  `argv` slot), the loop's frame slots (`end = q + 8·(|rest|+1)`, `ok = 1`, `&missing`), the
  library state (`stdout` has received `X` in total, `stderr` fresh, `StdVars`), the operands
  left (`ArgsAt`: from `q` on, `(p, n) :: rest`), `have_read_stdin = 0`, the guard, the return
  address;
* `LoopAt`: `LoopFr` at the call of `digest_file` (`0x2b81`) with its arguments.

`loop_mid` (`0x2b81` → `0x2c8a`): `MultiMid.mid_file` on the current operand, re-packaged:
`stdout` has received `X ++ fileLineM (dat n) n`.
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
open Silmaril.Elf.Link.Dyn.Imports

/-- **The operands left**: from the `argv` slot `q` on, each slot holds the pointer to its
name, a C string; slots and names in the argument area (`W.args`). -/
def ArgsAt (W : World) (m : Memory) : Word → List (Word × List Byte) → Prop
  | _, [] => True
  | q, (p, n) :: ops => loadN m q 8 = some p ∧ (∀ j, j < 8 → W.args (q.toNat + j)) ∧ CStr m p n ∧
      (∀ j, j < n.length + 1 → W.args (p.toNat + j)) ∧ ArgsAt W m (q + 8#64) ops

theorem ArgsAt.keep {W : World} {m m' : Memory} (hk : Keeps W.args m m') :
    ∀ {q : Word} {ops : List (Word × List Byte)}, ArgsAt W m q ops → ArgsAt W m' q ops
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨by rw [loadN_keeps hk h2]; exact h1, h2, cstr_keeps hk h3 h4, h4, ArgsAt.keep hk h5⟩

/-- **What the success tier asks of an operand name** (machine bytes): it does not start with
`-`, it contains no backslash, LF or CR (printed verbatim), and the file opens and reads
without error with contents `dat (toSpec n)`. -/
structure OpOk (E : Env) (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes)
    (n : List Byte) : Prop where
  nd : n.head? ≠ some 0x2d#8
  noEsc : ∀ c ∈ n, c ≠ 0x5c#8 ∧ c ≠ 0x0a#8 ∧ c ≠ 0x0d#8
  file : E.fs (toSpec n) = .ok (dat (toSpec n))
  /-- the file is within the library's stream bound (`Env.maxFile`) -/
  fit : (dat (toSpec n)).length ≤ E.maxFile

/-- The library has the resources for `c` more operands: a stream and a buffer for each. -/
def RoomN (E : Env) (g : Ghost) (c : Nat) : Prop :=
  InMain g ∧ g.allocs + c ≤ E.maxAllocs ∧ g.heap + 0x8048 * c ≤ E.maxHeap ∧ g.files + c ≤ E.maxOpen

theorem RoomN.mono {E : Env} {g : Ghost} {c c' : Nat} (h : RoomN E g c) (hc : c' ≤ c) : RoomN E g c' :=
  ⟨h.1, by have := h.2.1; omega, by have := h.2.2.1; have : 0x8048 * c' ≤ 0x8048 * c := Nat.mul_le_mul_left _ hc; omega,
    by have := h.2.2.2; omega⟩

/-- The result lines of the operands `ops`. -/
def linesM (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes)
    (ops : List (Word × List Byte)) : List Byte :=
  ops.flatMap fun pn => fileLineM (dat (toSpec pn.2)) pn.2

/-- What the operand loop needs of the world: `digest_file`'s imports, the result line's, the
stream laws the output path uses, reliable output, distinct `stdout`/`stderr`. -/
structure MultiImps (E : Env) (R : ShaRep) (W : World) (b lb kb sc : Word) : Prop where
  dig : DigImps E R W b lb kb
  pr : PrintImps E W b lb sc
  putc : PutcLaw E
  disj : StreamsDisj E
  apart : PrivApart E W
  footK : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a
  fw : E.stdoutF.toNat + 0x38 < 2 ^ 64
  rel : W.reliable = true
  ne : E.stdoutF ≠ E.stderrF

/-- Facts of `main`'s entry `s` the loop uses (constant along the run). -/
structure LoopCtx (E : Env) (W : World) (s : PState) : Prop where
  lo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat
  al : (s.m.core.read .rsp).toNat % 16 = 8
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)

/-- **The loop's invariant** at `ip` (`main`'s entry `s`; `q`: the current operand's `argv`
slot, `(p, n)`: its pointer and name, `rest`: the operands after it; `X`: what `stdout` has
received in total; `g`: the guard). -/
structure LoopFrO (E : Env) (W : World) (b lb kb sr sc : Word) (s x : PState) (ip q p : Word)
    (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte) (g : Word) (okv : Word) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) (reb s x.m.memory) x 328 4096 (sv6 (reb s x.m.memory))
  ma : ShaMainAll b x.m.memory
  bss : loadN x.m.memory (b + 0xa040#64) 1 = some 0#64
  bssw : x.m.memory.Permitted .write (b + 0xa040#64).toNat 1
  hr : loadN x.m.memory (b + 0xa160#64) 1 = some 0#64
  rip : x.m.core.rip = ip
  rbp : x.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rbx : x.m.core.read .rbx = s.m.core.read .rsp - 8#64 + 0xffffffffffffffa0#64
  r12 : x.m.core.read .r12 = p
  r14 : x.m.core.read .r14 = b + 0x7238#64
  r15 : x.m.core.read .r15 = q
  fs : x.m.core.fsBase = s.m.core.fsBase
  jobs : x.g.jobs = [.exitRax]
  atexit : x.g.atexit = [b + 0x69b0#64]
  guard : loadN x.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guards : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  out : ∃ st, StdoutIs E x.m.memory st ∧ st.err = false ∧ st.reading = false ∧ x.g.out ++ st.buf = X
  err : E.S.file x.m.memory E.stderrF (outSt 2)
  vars : StdVars E W lb x.m.memory
  tag : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 216) 1 = some [0#8]
  bin : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8]
  len : loadN x.m.memory (b + 0xa178#64) 8 = some 0x40#64
  endp : loadN x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64) 8 =
    some (q + BitVec.ofNat 64 (8 * (rest.length + 1)))
  qlim : q.toNat + 8 * (rest.length + 1) < 2 ^ 64
  ok : loadN x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 = some okv
  dsl : loadN x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff20#64) 8 =
    some (s.m.core.read .rsp - 8#64 + 0xffffffffffffff58#64)
  ret : x.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  args : ArgsAt W x.m.memory q ((p, n) :: rest)
  /-- the library's resources for the operands after this one -/
  res : RoomN E x.g rest.length

/-- The loop's invariant with the `ok` byte 1 (F7's success tier; `LoopFrO` holds any `ok`). -/
abbrev LoopFr (E : Env) (W : World) (b lb kb sr sc : Word) (s x : PState) (ip q p : Word)
    (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte) (g : Word) : Prop :=
  LoopFrO E W b lb kb sr sc s x ip q p n rest X g 1#64

/-- The invariant at the call of `digest_file` (`0x2b81`), with its arguments. -/
structure LoopAtO (E : Env) (W : World) (b lb kb sr sc : Word) (s x : PState) (q p : Word)
    (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte) (g : Word) (okv : Word) : Prop where
  fr : LoopFrO E W b lb kb sr sc s x (b + 0x2b81#64) q p n rest X g okv
  rdi : x.m.core.read .rdi = p
  rsi : x.m.core.read .rsi = s.m.core.read .rsp - 8#64 + 0xffffffffffffffa0#64
  rdx : x.m.core.read .rdx = s.m.core.read .rsp - 8#64 + 0xffffffffffffff58#64
  /-- … and for this one -/
  res : RoomN E x.g (rest.length + 1)

/-- `LoopAtO` with the `ok` byte 1. -/
abbrev LoopAt (E : Env) (W : World) (b lb kb sr sc : Word) (s x : PState) (q p : Word)
    (n : List Byte) (rest : List (Word × List Byte)) (X : List Byte) (g : Word) : Prop :=
  LoopAtO E W b lb kb sr sc s x q p n rest X g 1#64

/-- **A fresh body**: a body of `main` (any base `sR` with `main`'s entry registers) continues
from the base `reb s m'` at a state `x'` with the same stack pointer, `fsBase`, permissions,
saved registers and image facts. -/
theorem Body.freshK {W : World} {M : Memory → Prop} {s sR x x' : PState} {fr n : Nat}
    (h : Body W M sR x fr n (sv6 sR)) (hc : sR.m.core = s.m.core) (hn48 : 48 ≤ n)
    (hsp : x'.m.core.read .rsp = x.m.core.read .rsp) (hfs : x'.m.core.fsBase = x.m.core.fsBase)
    (hd : x'.g.done = none) (hp : ∀ acc a, x'.m.memory.permits acc a = x.m.memory.permits acc a)
    (hk : Keeps (fun a => (s.m.core.read .rsp).toNat - 48 ≤ a ∧ a < (s.m.core.read .rsp).toNat)
      x.m.memory x'.m.memory) (hM : M x'.m.memory) :
    Body W M (reb s x'.m.memory) x' fr n (sv6 (reb s x'.m.memory)) := by
  have hsv : sv6 (reb s x'.m.memory) = sv6 sR := by simp only [sv6, reb_core, hc]
  have hspR : sR.m.core.read .rsp = s.m.core.read .rsp := by rw [hc]
  have hroom := h.room
  rw [hspR] at hroom
  refine ⟨?_, Keeps.refl _ _, ?_, hM, ?_, hd, ?_, fun _ _ _ _ => rfl⟩
  · rw [hsp, h.rsp, hspR]; rfl
  · refine ⟨hroom.1, hroom.2.1, fun a h1 h2 => ?_⟩
    rw [hp, hp]; exact hroom.2.2 a h1 h2
  · rw [hfs, h.fs, hc]; rfl
  · intro q hq
    rw [hsv] at hq
    have hq' := h.saved q hq
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
    have h8 : 8 ≤ q.1 ∧ q.1 ≤ 48 := by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hsp8 : 48 ≤ (s.m.core.read .rsp).toNat := by have := hroom.1; omega
    show x'.m.memory.readBytes ((s.m.core.read .rsp).toNat - q.1) 8 = _
    rw [hk.readBytes (fun j hj => ⟨by omega, by omega⟩), ← hspR]
    exact hq'

theorem Body.fresh {W : World} {M : Memory → Prop} {s sR x : PState} {fr n : Nat}
    (h : Body W M sR x fr n (sv6 sR)) (hc : sR.m.core = s.m.core) (hn48 : 48 ≤ n) :
    Body W M (reb s x.m.memory) x fr n (sv6 (reb s x.m.memory)) :=
  Body.freshK h hc hn48 rfl rfl h.done (fun _ _ => rfl) (Keeps.refl _ _) h.mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **One operand, from the call of `digest_file` to the end of its line** (`0x2b81` →
`0x2c8a`): the invariant holds again at `0x2c8a`, `stdout` having received the operand's line. -/
theorem loop_mid {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {Q : PState → Prop} {v : PState} {q p g : Word} {n : List Byte} {rest : List (Word × List Byte)}
    {X : List Byte} {okv : Word} (h : LoopAtO E W b lb kb sr sc s v q p n rest X g okv) (hop : OpOk E dat n)
    (k : ∀ x, LoopFrO E W b lb kb sr sc s x (b + 0x2c8a#64) q p n rest (X ++ fileLineM (dat (toSpec n)) n) g okv →
      x.g.err = v.g.err → Keeps W.Kept v.m.memory x.m.memory →
      Keeps (fun a => (s.m.core.read .rsp).toNat + 8 ≤ a) v.m.memory x.m.memory →
      LibK E W v.m.memory x.m.memory → MustQ W Q x) : MustQ W Q v := by
  have F := h.fr
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  have hroom : Room W v.m.memory (s.m.core.read .rsp) 4096 := F.body.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := c.lo
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := F.args
  obtain ⟨sto, hso, hse, hsr, hsX⟩ := F.out
  refine mid_file M.dig M.pr M.putc M.disj M.apart (sB := reb s v.m.memory) (sp := s.m.core.read .rsp) rfl
    F.body F.ma F.rip F.rbp h.rdi F.r12 h.rsi F.rbx h.rdx F.r14 c.lo c.al (g := g)
    (by rw [F.fs]; exact F.guard) (by rw [F.fs]; exact c.guardk) hn3
    (fun j hj => Or.inr (Or.inl (hn4 j hj))) hop.nd hop.noEsc hop.file hso hse F.vars M.footK M.fw M.rel F.tag F.bin F.len
    ⟨h.res.1, by have := h.res.2.2.2; omega, hop.fit, by have := h.res.2.1; omega, by have := h.res.2.2.1; omega⟩ ?_
  intro x sR hcR hgR hBx hMAx hripx hregs hfsx hKx hstdout hjx hax hdx herrx hcnt hstreams hLx
  have hcs : sR.m.core = s.m.core := by rw [hcR]; rfl
  have hS : ∀ a, (s.m.core.read .rsp).toNat - 328 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ¬ ((s.m.core.read .rsp).toNat - 0x68 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 0x48) →
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 →
      ¬ ((s.m.core.read .rsp).toNat - 256 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 252) →
      a ≠ (s.m.core.read .rsp).toNat - 244 →
      (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 0x68 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 0x48) ∧
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 ∧
      ¬ ((s.m.core.read .rsp).toNat - 256 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 252) ∧
      a ≠ (s.m.core.read .rsp).toNat - 244 := fun a h1 _ h3 h4 h5 h6 => ⟨Or.inr h1, h3, h4, h5, h6⟩
  have hKK : Keeps W.Kept v.m.memory x.m.memory := hKx.mono fun a hK => by
    have := hKout a hK
    exact ⟨Or.inl hK, by omega, by omega, by omega, by omega⟩
  have hvx : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], x.m.core.read r = v.m.core.read r := hregs
  have e18 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64).toNat = (s.m.core.read .rsp).toNat - 240 :=
    (fp_neg _ 0xe8 (by omega) (by decide) (by decide)).trans (by omega)
  have e28 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64).toNat = (s.m.core.read .rsp).toNat - 224 :=
    (fp_neg _ 0xd8 (by omega) (by decide) (by decide)).trans (by omega)
  have e20 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff20#64).toNat = (s.m.core.read .rsp).toNat - 232 :=
    (fp_neg _ 0xe0 (by omega) (by decide) (by decide)).trans (by omega)
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I]; exact ha)
  have hIW : ∀ m : Nat, m < 0xa188 → ∀ j, j < 8 → m + j < 0xa188 →
      W.Kept ((b + BitVec.ofNat 64 m).toNat + j) := fun m hm j hj hmj =>
    hImgK _ (by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩)
  obtain ⟨st', hs', he', hr', hX'⟩ := hstdout
  refine k x ⟨Body.fresh hBx hcs (by decide), hMAx,
    by rw [loadN_keeps hKK (fun j hj => hIW 0xa040 (by decide) j (by omega) (by omega))]; exact F.bss,
    (hKK.permitted (fun j hj => hIW 0xa040 (by decide) j (by omega) (by omega))).2 F.bssw,
    by rw [loadN_keeps hKK (fun j hj => hIW 0xa160 (by decide) j (by omega) (by omega))]; exact F.hr,
    hripx, by rw [hvx .rbp (by simp)]; exact F.rbp, by rw [hvx .rbx (by simp)]; exact F.rbx,
    by rw [hvx .r12 (by simp)]; exact F.r12, by rw [hvx .r14 (by simp)]; exact F.r14,
    by rw [hvx .r15 (by simp)]; exact F.r15, hfsx.trans F.fs, by rw [hjx]; exact F.jobs,
    by rw [hax]; exact F.atexit,
    by rw [loadN_keeps hKK (fun j hj => c.guardk j hj)]; exact F.guard, ?_,
    ⟨st', hs', he', by rw [hr', hsr], by rw [hX', hsX]⟩,
    hstreams _ _ (Ne.symm M.ne) F.err, F.vars.keepR (hKK.mono fun a ha => ?_), ?_, ?_,
    by rw [loadN_keeps hKK (fun j hj => hIW 0xa178 (by decide) j (by omega) (by omega))]; exact F.len,
    ?_, F.qlim, ?_, ?_, ?_, ArgsAt.keep (hKK.mono fun a h => Or.inr (Or.inl h)) ⟨hn1, hn2, hn3, hn4, hn5⟩,
    ⟨⟨[], by rw [hjx]; exact F.jobs⟩, by have := h.res.2.1; omega, by have := h.res.2.2.1; rw [hcnt.2.1]; omega,
      by have := h.res.2.2.2; omega⟩⟩ herrx hKK
    (hKx.mono fun a ha => ⟨Or.inr (by omega), by omega, by omega, by omega, by omega⟩) hLx
  · rw [hKx.readBytes (fun j hj => hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.guards
  · have := F.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
    rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
      simp only [VarR] at ha; omega] at this
  · rw [hKx.readBytes (fun j hj => hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.tag
  · rw [hKx.readBytes (fun j hj => hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.bin
  · rw [loadN_keeps hKx (fun j hj => by
      rw [e18]; exact hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.endp
  · rw [loadN_keeps hKx (fun j hj => by
      rw [e28]; exact hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.ok
  · rw [loadN_keeps hKx (fun j hj => by
      rw [e20]; exact hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.dsl
  · rw [hKx.readBytes (fun j hj => hS _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact F.ret

end Silmaril.Elf.Link.Dyn.Sha256sum
