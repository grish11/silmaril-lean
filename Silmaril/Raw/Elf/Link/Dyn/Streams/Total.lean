module

public import Silmaril.Raw.Elf.Link.Dyn.Streams.Rep
public import Silmaril.Raw.Elf.Link.Dyn.Imports.ShaRep
public import Silmaril.Elf.Link.Dyn.Streams.Extra
public import Silmaril.Elf.Link.Dyn.Streams.Errors

/-! # The stream contracts are satisfiable (`Streams.Defs`, non-vacuity)

For the concrete environment `envOf fs optA` (the stream representation `slotRep`, `stdout` and
`stderr` in the first two slots, any file system `fs`), every contract of `shaContracts` has an
outcome from every state of a world whose kept addresses avoid the library's arena — under the
extra hypotheses `Fixes` (F1–F5), each of which is a precondition strengthening of one contract
(a contract `Contract (pre ∧ H) post` is total iff the contract has an outcome whenever `H`).
Two more room assumptions, of the same kind as F3: `malloc` (with `allocOk`) needs an unmapped range
below the arena for its block (`hheap`), and a refused `fopen` writes `errno`, whose cell `eA` (the
first word of the last slot) must hold no stream (`hefree`).
Main result: `shaContracts_total`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams.Total

open Silmaril.X86 (Word Byte Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.Ext (loadN leBytes leValue)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Imports

/-- The concrete `errno`: the first word of the last slot (reserved: no stream lives there when a
call can fail with `errno`). -/
def eA : Nat := A0 + (K0 - 1) * S0

/-- The concrete resource bounds: four `malloc` requests of 64 KiB in total, four `fopen`s (of
files whose unread bytes fit a slot). -/
def mAllocs : Nat := 4
def mHeap : Nat := 0x10000
def mOpen : Nat := 4

/-- The concrete environment. -/
def envOf (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word) :
    Env where
  S := slotRep
  stdoutF := BitVec.ofNat 64 A0
  stderrF := BitVec.ofNat 64 (A0 + S0)
  fs := fs
  optindA := optA
  errnoA := BitVec.ofNat 64 eA
  maxAllocs := mAllocs
  maxHeap := mHeap
  maxOpen := mOpen
  maxFile := S0 - 64

/-- A return with result `v`, memory `m` and library state `g`. -/
def retM (s : PState) (v : Word) (m : Memory) (g : Ghost) : PState :=
  ⟨⟨(retState s v g).m.core, m⟩, g⟩

theorem retM_fs (s : PState) (v : Word) (m : Memory) (g : Ghost) :
    (retM s v m g).m.core.fsBase = s.m.core.fsBase := rfl

/-- A return that leaves memory alone meets every library frame. -/
theorem libRet_same (E : Env) (W : World) (fp : Nat → Prop) (s : PState) (v : Word) (g : Ghost)
    (hp : ∀ m, E.S.priv m = E.S.priv s.m.memory) :
    LibRet E W fp s (retM s v s.m.memory g) :=
  ⟨⟨(retState_returns W s v g).1, Keeps.refl _ _⟩, rfl, fun _ _ _ _ => rfl, Keeps.refl _ _,
    fun a h => Or.inl (by rw [hp] at h; exact h), fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ st h => Or.inl ⟨st, h⟩⟩

theorem others_same (E : Env) (s : PState) (v : Word) (g : Ghost) (fs : List Word) :
    OthersKept E s (retM s v s.m.memory g) fs := fun _ _ _ h => h

theorem priv_const (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (optA : Word) (m m' : Memory) : (envOf fs optA).S.priv m = (envOf fs optA).S.priv m' := rfl

/-! ## Uniqueness -/

theorem leBytes_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : leBytes (BitVec.ofNat 64 a) 8 = leBytes (BitVec.ofNat 64 b) 8) : a = b := by
  have := congrArg leValue h
  simp only [Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (by omega)] at this

theorem flagsN_inj (r f e x r' f' e' x' : Bool)
    (h : (if r then 1 else 0) + (if f then 2 else 0) + (if e then 16 else 0) + (if x then 32 else 0) =
      (if r' then 1 else 0) + (if f' then 2 else 0) + (if e' then 16 else 0) + (if x' then 32 else 0)) :
    r = r' ∧ f = f' ∧ e = e' ∧ x = x' := by
  revert h
  cases r <;> cases f <;> cases e <;> cases x <;> cases r' <;> cases f' <;> cases e' <;> cases x' <;>
    simp

theorem flagsN_lt (st : St) : flagsN st < 2 ^ 64 := by
  unfold flagsN; split <;> split <;> split <;> split <;> omega

theorem enc_inj {st1 st2 : St} (h1 : Valid st1) (h2 : Valid st2) (h : enc st1 = enc st2) : st1 = st2 := by
  have hh : hdr st1 = hdr st2 := by
    have := congrArg (List.take 64) h
    simpa [enc, List.take_append_of_le_length, hdr_length] using this
  have hr : st1.rd = st2.rd := by
    have := congrArg (List.drop 64) h
    simpa [enc, hdr_length] using this
  simp only [hdr, List.append_assoc] at hh
  have e1 := List.append_inj hh (by simp [leBytes])
  have e2 := List.append_inj e1.2 (by simp [leBytes])
  have hf := leBytes_inj (flagsN_lt st1) (flagsN_lt st2) e1.1
  have hd := leBytes_inj h1.2.1 h2.2.1 e2.1
  obtain ⟨b1, b2, b3, b4⟩ := flagsN_inj _ _ _ _ _ _ _ _ hf
  rcases st1 with ⟨fd, reading, rd, fail, eof, err, buf⟩
  rcases st2 with ⟨fd', reading', rd', fail', eof', err', buf'⟩
  obtain ⟨hb1, -, -⟩ := h1
  obtain ⟨hb2, -, -⟩ := h2
  simp_all

theorem fileR_unique {m : Memory} {f : Word} {st1 st2 : St} (h1 : fileR m f st1) (h2 : fileR m f st2) :
    st1 = st2 := by
  have hl : st1.rd.length = st2.rd.length := by rw [← lenAt_of h1, ← lenAt_of h2]
  have := h1.2.2.1
  rw [hl, h2.2.2.1] at this
  exact enc_inj h1.2.1 h2.2.1 (Option.some.inj this).symm

theorem cstr_unique {m : Memory} {a : Word} {p q : List Byte} (hp : CStr m a p) (hq : CStr m a q) :
    p = q := by
  obtain ⟨hp0, hpr⟩ := hp
  obtain ⟨hq0, hqr⟩ := hq
  by_contra hne
  rcases Nat.lt_or_ge p.length q.length with hlt | hge
  · have := sub_read hqr (k := 0) (j := p.length + 1) (by omega) (by omega)
    simp only [Nat.add_zero, List.drop_zero] at this
    rw [hpr, Option.some.injEq] at this
    have h0 := congrArg (·[p.length]?) this
    simp only [List.getElem?_append_right (le_refl _), Nat.sub_self] at h0
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_append_left hlt] at h0
    exact hq0 _ (List.mem_of_getElem? h0.symm) rfl
  · rcases Nat.lt_or_ge q.length p.length with hlt' | hge'
    · have := sub_read hpr (k := 0) (j := q.length + 1) (by omega) (by omega)
      simp only [Nat.add_zero, List.drop_zero] at this
      rw [hqr, Option.some.injEq] at this
      have h0 := congrArg (·[q.length]?) this
      simp only [List.getElem?_append_right (le_refl _), Nat.sub_self] at h0
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_append_left hlt'] at h0
      exact hp0 _ (List.mem_of_getElem? h0.symm) rfl
    · have hl : p.length = q.length := by omega
      rw [hl, hqr] at hpr
      exact hne (List.append_cancel_right (Option.some.inj hpr)).symm

/-! ## Writes at writable addresses keep every stream (streams are read-only to writers) -/

theorem writable_of {m : Memory} {a n : Nat} (h : m.Permitted .write a n) :
    ∀ k < n, m.permits .write (a + k) = true := by
  unfold Memory.Permitted at h; rw [Memory.checkSpan_iff] at h; exact h.2.2

theorem put_keeps_ro {m : Memory} {a : Nat} {l : List Byte}
    (hw : ∀ k < l.length, m.permits .write (a + k) = true) {f n : Nat}
    (hro : ∀ k < n, m.permits .write (f + k) = false) :
    Keeps (fun x => f ≤ x ∧ x < f + n) m (putBytes m a l) :=
  putBytes_keeps fun x hx => by
    by_contra hc
    have h1 := hw (x - a) (by omega)
    have h2 := hro (x - f) (by omega)
    rw [show a + (x - a) = x by omega] at h1
    rw [show f + (x - f) = x by omega, h1] at h2
    exact absurd h2 (by decide)

theorem fileR_put {m : Memory} {a : Nat} {l : List Byte}
    (hw : ∀ k < l.length, m.permits .write (a + k) = true) {f : Word} {st : St} :
    fileR (putBytes m a l) f st ↔ fileR m f st := by
  constructor
  · intro h
    have hro : ∀ k < 64 + st.rd.length, m.permits .write (f.toNat + k) = false := h.2.2.2
    have hk := put_keeps_ro hw hro
    refine ⟨h.1, h.2.1, ?_, hro⟩
    rw [← hk.readBytes (fun k hk' => ⟨by omega, by omega⟩)]; exact h.2.2.1
  · intro h
    have hk := put_keeps_ro hw h.2.2.2
    exact ⟨h.1, h.2.1, by rw [hk.readBytes (fun k hk' => ⟨by omega, by omega⟩)]; exact h.2.2.1, h.2.2.2⟩

/-! ## Contracts that leave memory alone -/

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word)
  (W : World) (s : PState)

local notation "E" => envOf fs optA

theorem retM_rax (s : PState) (v : Word) (m : Memory) (g : Ghost) :
    (retM s v m g).m.core.read .rax = v := by simp [retM, retState]

theorem low32_ofNat (n : Nat) : low32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp [low32]

theorem libRet0 (fp : Nat → Prop) (v : Word) (g : Ghost) : LibRet E W fp s (retM s v s.m.memory g) :=
  libRet_same _ W fp s v g (fun _ => rfl)

theorem quiet_ok (P : Word → Prop) (hP : P 0#64) : ∃ r, quietLib E W P s r :=
  ⟨.ok (retM s 0#64 s.m.memory s.g), fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _,
    by rw [retM_rax]; exact hP, rfl, others_same _ _ _ _ _⟩⟩

theorem fadvise_ok : ∃ r, fadviseStep E W s r := quiet_ok fs optA W s _ trivial
theorem lseek_ok : ∃ r, lseekStep E W s r := quiet_ok fs optA W s _ trivial

theorem setvbuf_ok : ∃ r, setvbufStep E W s r :=
  ⟨.ok (retM s 0#64 s.m.memory s.g), fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _, rfl,
    others_same _ _ _ _ _⟩⟩

theorem free_ok : ∃ r, freeStep E W s r :=
  ⟨.ok (retM s 0#64 s.m.memory { s.g with blocks := s.g.blocks.eraseP (·.1 == (s.m.core.read .rdi).toNat) }),
    fun _ => ⟨_, rfl, ⟨⟨(retState_returns W s _ _).1, Keeps.refl _ _⟩, rfl, fun _ _ _ _ => rfl, Keeps.refl _ _,
      fun _ h => Or.inl h, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ st h => Or.inl ⟨st, h⟩⟩, rfl,
      others_same _ _ _ _ _⟩⟩

theorem fileno_ok : ∃ r, filenoStep E W s r := by
  by_cases h : ∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st
  · obtain ⟨st, hst⟩ := h
    refine ⟨.ok (retM s (BitVec.ofNat 64 st.fd) s.m.memory s.g), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _, fun st' h' => ?_⟩⟩
    rw [← fileR_unique hst h', retM_rax, low32_ofNat]
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem freading_ok : ∃ r, freadingStep E W s r := by
  by_cases h : ∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st
  · obtain ⟨st, hst⟩ := h
    refine ⟨.ok (retM s (if st.reading then 1#64 else 0#64) s.m.memory s.g), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _, fun st' h' => ?_⟩⟩
    rw [← fileR_unique hst h', retM_rax]
    cases st.reading <;> decide
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem fpending_ok : ∃ r, fpendingStep E W s r := by
  by_cases h : ∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st
  · obtain ⟨st, hst⟩ := h
    refine ⟨.ok (retM s (BitVec.ofNat 64 st.buf.length) s.m.memory s.g), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _, fun st' h' => ?_⟩⟩
    rw [← fileR_unique hst h', retM_rax]
    exact ⟨hst, rfl⟩
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem error_ok : ∃ r, errorStep E W s r := by
  by_cases h0 : low32 (s.m.core.read .rdi) = 0#32
  · refine ⟨.ok (retM s 0#64 s.m.memory s.g), fun _ => ⟨_, rfl, ?_⟩⟩
    beta_reduce; rw [ite_eq_left h0]
    exact ⟨libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _⟩
  · refine ⟨.ok (gateState W s { s.g with jobs := [.exit (s.m.core.read .rdi)] }), fun _ => ⟨_, rfl, ?_⟩⟩
    beta_reduce; rw [ite_eq_right h0]
    exact ⟨gateState_at W s _, rfl⟩

/-- Output that goes straight to file descriptor 1 (`stdout` is never buffered here). -/
theorem appended_same (new : List Byte) (v : Word) (g : Ghost) (hg : g.out = s.g.out ++ new) :
    Appended E W s (retM s v s.m.memory g) new := by
  intro st hst
  refine ⟨st, hst, rfl, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  have hb : st.buf = [] := hst.1.2.1.1
  show g.out ++ st.buf = s.g.out ++ st.buf ++ new
  rw [hb, hg]; simp

def outG (s : PState) (new : List Byte) : Ghost := { s.g with out := s.g.out ++ new, done := none }

theorem ghostOut (new : List Byte) (v : Word) : GhostOut s (retM s v s.m.memory (outG s new)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem printfHex_ok : ∃ r, printfHexStep E W s r :=
  ⟨.ok (retM s 0#64 s.m.memory (outG s (hex2 ((s.m.core.read .rdx).setWidth 8)))), fun _ => ⟨_, rfl,
    libRet0 fs optA W s _ _ _, ghostOut s _ _, others_same _ _ _ _ _, appended_same fs optA W s _ _ _ rfl⟩⟩

theorem overflow_ok : ∃ r, overflowStep E W s r :=
  ⟨.ok (retM s 0#64 s.m.memory (outG s [(s.m.core.read .rsi).setWidth 8])), fun _ => ⟨_, rfl,
    libRet0 fs optA W s _ _ _, ghostOut s _ _, others_same _ _ _ _ _, appended_same fs optA W s _ _ _ rfl⟩⟩

theorem fwrite_ok : ∃ r, fwriteStep E W s r := by
  by_cases h : ∃ d, s.m.memory.readBytes (s.m.core.read .rdi).toNat
      ((s.m.core.read .rsi).toNat * (s.m.core.read .rdx).toNat) = some d
  · obtain ⟨d, hd⟩ := h
    refine ⟨.ok (retM s (s.m.core.read .rdx) s.m.memory (outG s d)), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, ghostOut s _ _, others_same _ _ _ _ _, fun d' h' => ?_⟩⟩
    rw [hd, Option.some.injEq] at h'
    subst h'
    exact ⟨appended_same fs optA W s _ _ _ rfl, fun _ => retM_rax _ _ _ _⟩
  · exact ⟨.stop, fun hp => absurd hp.2.2.2 h⟩

theorem fflush_ok : ∃ r, fflushStep E W s r := by
  by_cases h : ∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st
  · obtain ⟨st, hst⟩ := h
    have hb : st.buf = [] := hst.2.1.1
    refine ⟨.ok (retM s 0#64 s.m.memory (outG s [])), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, ghostOut s _ _, others_same _ _ _ _ _, fun st' h' => ?_⟩⟩
    obtain rfl := fileR_unique hst h'
    have hst' : { st with buf := [] } = st := by rw [← hb]
    refine ⟨fun _ => Or.inl ⟨by simp [retM, outG, hb], by rw [hst']; exact hst, fun _ => ?_⟩,
      fun _ => ⟨by simp [retM, outG], by rw [hst']; exact hst, fun _ => ?_⟩⟩ <;>
      rw [retM_rax] <;> rfl
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem fclose_ok : ∃ r, fcloseStep E W s r := by
  by_cases h : ∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st
  · obtain ⟨st, hst⟩ := h
    have hb : st.buf = [] := hst.2.1.1
    refine ⟨.ok (retM s 0#64 s.m.memory (outG s [])), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, others_same _ _ _ _ _, fun st' h' => ?_⟩⟩
    obtain rfl := fileR_unique hst h'
    refine ⟨fun _ => Or.inl ⟨by simp [retM, outG, hb], fun _ => ?_⟩, fun _ => ⟨by simp [retM, outG], fun _ => ?_⟩⟩ <;>
      rw [retM_rax] <;> rfl
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

end

/-! ## Strings, `getopt_long`, and the `Imports` contracts with the library frame -/

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word)
  (W : World) (s : PState)

local notation "E" => envOf fs optA

theorem strrchr_ok : ∃ r, strrchrStep E W s r := by
  by_cases h : ∃ str, CStr s.m.memory (s.m.core.read .rdi) str
  · obtain ⟨str, hs⟩ := h
    let c := (s.m.core.read .rsi).setWidth 8
    let v : Word := ((List.range (str.length + 1)).reverse.find? (fun i => (str ++ [0])[i]? = some c)).elim
      0#64 (fun i => s.m.core.read .rdi + BitVec.ofNat 64 i)
    refine ⟨.ok (retM s v s.m.memory s.g), fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _, rfl,
      others_same _ _ _ _ _, fun str' h' => ?_⟩⟩
    obtain rfl := cstr_unique hs h'
    simp only [retM_rax, v]
    split <;> rename_i heq <;> simp only [c, heq, Option.elim_some, Option.elim_none]
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem strncmp_ok : ∃ r, strncmpStep E W s r := by
  by_cases h : (∃ a, CStr s.m.memory (s.m.core.read .rdi) a) ∧ ∃ b, CStr s.m.memory (s.m.core.read .rsi) b
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    let n := (s.m.core.read .rdx).toNat
    let C : Prop := (a ++ [0]).take n = (b ++ [0]).take n ∨
      ((a ++ [0]).takeWhile (· ≠ 0)).take n = ((b ++ [0]).takeWhile (· ≠ 0)).take n
    refine ⟨.ok (retM s (if C then 0#64 else 1#64) s.m.memory s.g), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _, fun a' b' ha' hb' => ?_⟩⟩
    obtain rfl := cstr_unique ha ha'
    obtain rfl := cstr_unique hb hb'
    rw [retM_rax]
    by_cases hC : C
    · rw [ite_eq_left hC]; exact ⟨fun _ => hC, fun _ => rfl⟩
    · rw [ite_eq_right hC]; exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 hC⟩
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

/-- `framed` around a contract whose outcome leaves memory alone. -/
theorem framed_same (fp : PState → Nat → Prop) (c : PState → Res PState → Prop) (v : Word) (g : Ghost)
    (hc : c s (.ok (retM s v s.m.memory g))) : ∃ r, framed E W fp c s r :=
  ⟨_, hc, fun _ t ht => by cases ht; exact ⟨libRet0 fs optA W s _ _ _, others_same _ _ _ _ _⟩,
    fun t ht => by cases ht; exact ⟨fun _ _ _ _ _ => rfl, fun _ st h => Or.inl ⟨st, h⟩⟩⟩

theorem framed_quiet (fp : PState → Nat → Prop) : ∃ r, framed E W fp (quietStep W fun _ => True) s r :=
  framed_same fs optA W s fp _ 0#64 s.g fun _ => ⟨_, rfl, retState_returns W s _ _, trivial, rfl⟩

theorem framed_cxa (fp : PState → Nat → Prop) : ∃ r, framed E W fp (cxaAtexitStep W) s r :=
  framed_same fs optA W s fp _ 1#64 s.g fun _ => ⟨_, rfl, retState_returns W s _ _,
    Or.inr ⟨by rw [retM_rax]; decide, rfl⟩⟩

section put
variable {v : Word} {a : Nat} {l : List Byte} (hw : ∀ k < l.length, s.m.memory.permits .write (a + k) = true)
include hw

/-- A call that writes `l` at writable addresses keeps every stream and opens none. -/
theorem others_putW (fsl : List Word) : OthersKept E s (retPut s v a l) fsl :=
  fun _ _ _ h => (fileR_put hw).mpr h

theorem noNew_put (fp : Nat → Prop) : NoNewStream E fp s (retPut s v a l) :=
  fun _ st h => Or.inl ⟨st, (fileR_put hw).mp h⟩

theorem libRet_put (fp : Nat → Prop) (hfp : ∀ x, a ≤ x → x < a + l.length → fp x) :
    LibRet E W fp s (retPut s v a l) :=
  ⟨retPut_except W s v a l fp hfp, rfl, fun _ _ _ _ => rfl, putBytes_keeps fun x hx => by
    by_contra hc; exact hx.2.1 (hfp x (by omega) (by omega)), fun _ h => Or.inl h, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, noNew_put fs optA s hw fp⟩

end put

theorem noMap_put (fp : Nat → Prop) (v : Word) (a : Nat) (l : List Byte) :
    NoMap E fp s (retPut s v a l) := fun _ _ _ _ _ => rfl

open ShaState in
theorem framed_init :
    ∃ r, framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256InitStep shaRep W) s r := by
  by_cases hp : s.m.memory.Permitted .write (s.m.core.read .rdi).toNat 112
  · have hl := ShaState.enc_length _ (sig_ok [])
    have hin : ∀ x, (s.m.core.read .rdi).toNat ≤ x → x < (s.m.core.read .rdi).toNat + (ShaState.enc (sig [])).length →
        ctxRange (s.m.core.read .rdi) x := fun x h1 h2 => ⟨h1, by rw [hl] at h2; exact h2⟩
    have hw : ∀ k < (ShaState.enc (sig [])).length,
        s.m.memory.permits .write ((s.m.core.read .rdi).toNat + k) = true :=
      fun k hk => writable_of hp k (by rw [hl] at hk; exact hk)
    refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (ShaState.enc (sig []))), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩,
      fun _ t ht => ?_, fun t ht => ?_⟩
    · exact retPut_except W s _ _ _ _ hin
    · exact ⟨_, putBytes_ctx _ _ _ hl, dec_enc _ (sig_ok _)⟩
    · cases ht
      exact ⟨libRet_put fs optA W s hw _ hin, others_putW fs optA s hw _⟩
    · cases ht
      exact ⟨noMap_put fs optA s (fun _ => False) _ _ _, noNew_put fs optA s hw (fun _ => False)⟩
  · exact ⟨.stop, fun h => absurd h.2 hp, fun _ t ht => (by cases ht), fun t ht => (by cases ht)⟩

open ShaState in
theorem framed_update :
    ∃ r, framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256UpdateStep shaRep W) s r := by
  by_cases hp : (∃ m, shaRep.holds s.m.memory (s.m.core.read .rdi) m) ∧
      (∃ d, s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some d) ∧
      s.m.memory.Permitted .write (s.m.core.read .rdi).toNat 112
  · obtain ⟨⟨m0, bs0, hb0, hd0⟩, ⟨d0, hr0⟩, hpw⟩ := hp
    let σ := (sig (m0.map UInt8.ofBitVec)).step (d0.map UInt8.ofBitVec)
    have hσ : σ.Ok := step_ok _ _
    have hl := ShaState.enc_length _ hσ
    have hin : ∀ x, (s.m.core.read .rdi).toNat ≤ x → x < (s.m.core.read .rdi).toNat + (ShaState.enc σ).length →
        ctxRange (s.m.core.read .rdi) x := fun x h1 h2 => ⟨h1, by rw [hl] at h2; exact h2⟩
    have hw : ∀ k < (ShaState.enc σ).length,
        s.m.memory.permits .write ((s.m.core.read .rdi).toNat + k) = true :=
      fun k hk => writable_of hpw k (by rw [hl] at hk; exact hk)
    refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (ShaState.enc σ)), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩,
      fun _ t ht => ?_, fun t ht => ?_⟩
    · exact retPut_except W s _ _ _ _ hin
    · rintro m d ⟨bs, hb, hd⟩ hr
      obtain rfl := ctxBytes_unique hb hb0
      obtain rfl : d = d0 := Option.some.inj (hr.symm.trans hr0)
      refine ⟨_, putBytes_ctx _ _ _ hl, ?_⟩
      rw [dec_enc _ hσ, List.map_append, sig_append, ← hd, hd0]
    · cases ht
      exact ⟨libRet_put fs optA W s hw _ hin, others_putW fs optA s hw _⟩
    · cases ht
      exact ⟨noMap_put fs optA s (fun _ => False) _ _ _, noNew_put fs optA s hw (fun _ => False)⟩
  · exact ⟨.stop, fun h => absurd ⟨h.2.1, h.2.2.1, h.2.2.2⟩ hp, fun _ t ht => (by cases ht),
      fun t ht => (by cases ht)⟩

theorem framed_final :
    ∃ r, framed E W (fun s a => ctxRange (s.m.core.read .rsi) a ∨
      ((s.m.core.read .rdi).toNat ≤ a ∧ a < (s.m.core.read .rdi).toNat + 32)) (sha256FinalStep shaRep W) s r := by
  by_cases hp : (∃ m, shaRep.holds s.m.memory (s.m.core.read .rsi) m) ∧
      s.m.memory.Permitted .read (s.m.core.read .rdi).toNat 32 ∧
      s.m.memory.Permitted .write (s.m.core.read .rdi).toNat 32
  · obtain ⟨⟨m0, bs0, hb0, hd0⟩, hrd, hpw⟩ := hp
    have hl : (sha256 m0).length = 32 := by simp [sha256, Silmaril.Crypto.SHA256.digest_length]
    have hin : ∀ x, (s.m.core.read .rdi).toNat ≤ x → x < (s.m.core.read .rdi).toNat + (sha256 m0).length →
        ctxRange (s.m.core.read .rsi) x ∨
          ((s.m.core.read .rdi).toNat ≤ x ∧ x < (s.m.core.read .rdi).toNat + 32) :=
      fun x h1 h2 => Or.inr ⟨h1, by rw [hl] at h2; exact h2⟩
    have hw : ∀ k < (sha256 m0).length,
        s.m.memory.permits .write ((s.m.core.read .rdi).toNat + k) = true :=
      fun k hk => writable_of hpw k (by rw [hl] at hk; exact hk)
    refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (sha256 m0)), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩,
      fun _ t ht => ?_, fun t ht => ?_⟩
    · exact retPut_except W s _ _ _ _ hin
    · rintro m ⟨bs, hb, hd⟩
      obtain rfl := ctxBytes_unique hb hb0
      rw [sha256_eq (hd.symm.trans hd0)]
      unfold Memory.Permitted at hrd
      rw [Memory.checkSpan_iff] at hrd
      obtain ⟨ha, hw', hpm⟩ := hrd
      have := readWith_of_points (mem := (retPut s 1#64 (s.m.core.read .rdi).toNat (sha256 m0)).m.memory)
        (acc := .read) (l := sha256 m0) (a := (s.m.core.read .rdi).toNat)
        (by rw [hl]; exact hw') ha (fun k hk => ⟨hpm k (by rw [hl] at hk; exact hk),
          Memory.install_get _ _ _ _ hk⟩)
      simpa [Memory.readBytes, hl] using this
    · cases ht
      exact ⟨libRet_put fs optA W s hw _ hin, others_putW fs optA s hw _⟩
    · cases ht
      exact ⟨noMap_put fs optA s (fun _ => False) _ _ _, noNew_put fs optA s hw (fun _ => False)⟩
  · exact ⟨.stop, fun h => absurd ⟨h.2.1, h.2.2.2.1, h.2.2.1⟩ hp, fun _ t ht => (by cases ht),
      fun t ht => (by cases ht)⟩

theorem getopt_ok : ∃ r, getoptNoneStep E W s r := by
  by_cases hp : s.m.memory.Permitted .read optA.toNat 4 ∧ s.m.memory.Permitted .write optA.toNat 4
  · obtain ⟨hr, hpw⟩ := hp
    have hl : (leBytes 1#64 4).length = 4 := by simp [leBytes]
    have hin : ∀ x, optA.toNat ≤ x → x < optA.toNat + (leBytes 1#64 4).length →
        optA.toNat ≤ x ∧ x < optA.toNat + 4 := fun x h1 h2 => ⟨h1, by rw [hl] at h2; exact h2⟩
    have hw : ∀ k < (leBytes 1#64 4).length, s.m.memory.permits .write (optA.toNat + k) = true :=
      fun k hk => writable_of hpw k (by rw [hl] at hk; exact hk)
    refine ⟨.ok (retPut s 0xffffffff#64 optA.toNat (leBytes 1#64 4)), fun _ => ⟨_, rfl,
      libRet_put fs optA W s hw _ hin, rfl, others_putW fs optA s hw _, rfl, ?_⟩⟩
    unfold Memory.Permitted at hr
    rw [Memory.checkSpan_iff] at hr
    obtain ⟨ha, hw', hpm⟩ := hr
    have := readWith_of_points (mem := (retPut s 0xffffffff#64 optA.toNat (leBytes 1#64 4)).m.memory)
      (acc := .read) (l := leBytes 1#64 4) (a := optA.toNat)
      (by rw [hl]; exact hw') ha (fun k hk => ⟨hpm k (by rw [hl] at hk; exact hk),
        Memory.install_get _ _ _ _ hk⟩)
    rw [hl] at this
    show Option.map _ (Memory.readWith _ .read optA.toNat 4) = _
    rw [this]
    simp [Silmaril.X86.Ext.leValue_leBytes]
  · exact ⟨.stop, fun h => absurd ⟨h.2.1, h.2.2.1⟩ hp⟩

end

/-! ## `fread` -/

theorem read_put {m : Memory} {a : Nat} {l : List Byte} (ha : a < 2 ^ 64) (hw : a + l.length ≤ 2 ^ 64)
    (hp : ∀ k < l.length, m.permits .read (a + k) = true) :
    (putBytes m a l).readBytes a l.length = some l := by
  have := readWith_of_points (mem := putBytes m a l) (acc := .read) (l := l) (a := a) hw ha
    (fun k hk => ⟨hp k hk, Memory.install_get _ _ _ _ hk⟩)
  simpa [Memory.readBytes] using this

theorem readSt_fst_length (st : St) (k : Nat) : (readSt st k).1.length ≤ k := by
  unfold readSt; dsimp only; split <;> simp

theorem readSt_valid {st : St} (h : Valid st) (k : Nat) : Valid (readSt st k).2 ∧
    (readSt st k).2.rd.length ≤ st.rd.length := by
  obtain ⟨hb, hf, hl⟩ := h
  unfold readSt; dsimp only; split
  · exact ⟨⟨hb, hf, by simp; omega⟩, by simp⟩
  · exact ⟨⟨hb, hf, by simp; omega⟩, by simp⟩

theorem slot_disjoint {f f' : Word} (hf : IsSlot f) (hf' : IsSlot f') (hne : f ≠ f') {x : Nat}
    (hx1 : f'.toNat ≤ x) (hx2 : x < f'.toNat + S0) : x < f.toNat ∨ f.toNat + S0 ≤ x := by
  obtain ⟨k, hk, he⟩ := hf
  obtain ⟨k', hk', he'⟩ := hf'
  have hkk : k ≠ k' := fun h => hne (BitVec.eq_of_toNat_eq (by rw [he, he', h]))
  unfold S0 at *; unfold A0 at *
  rcases Nat.lt_or_gt_of_ne hkk with h | h
  · right; have : (k + 1) * 1048576 ≤ k' * 1048576 := Nat.mul_le_mul_right _ h; rw [Nat.succ_mul] at this; omega
  · left; have : (k' + 1) * 1048576 ≤ k * 1048576 := Nat.mul_le_mul_right _ h; rw [Nat.succ_mul] at this; omega

theorem foot_in_slot {m : Memory} {f : Word} {st : St} (h : fileR m f st) {x : Nat} (hx : footR m f x) :
    f.toNat ≤ x ∧ x < f.toNat + S0 := by
  have hl := lenAt_of h
  have := h.2.1.2.2
  unfold footR at hx; rw [hl] at hx; omega

/-- A stream survives a change of memory that keeps its slot. -/
theorem fileR_keep_slot {m m' : Memory} {f : Word} {st : St} (h : fileR m f st)
    (hk : ∀ x, f.toNat ≤ x → x < f.toNat + S0 → m'.bytes.get? x = m.bytes.get? x ∧ ∀ acc, m'.permits acc x = m.permits acc x) :
    fileR m' f st := by
  have hS := h.2.1.2.2
  refine ⟨h.1, h.2.1, ?_, fun k hk' => by rw [(hk _ (by omega) (by omega)).2]; exact h.2.2.2 k hk'⟩
  rw [Keeps.readBytes (P := fun x => f.toNat ≤ x ∧ x < f.toNat + S0) (fun x hx => hk x hx.1 hx.2)
    (fun k hk' => ⟨by omega, by omega⟩)]
  exact h.2.2.1

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word)
  (W : World) (s : PState)

local notation "E" => envOf fs optA

/-- **`fread` is total** in worlds whose kept addresses avoid the arena. -/
theorem freadGen_ok (hW : ∀ a, W.Kept a → ¬ Arena a) (ptr size n f : Word) :
    ∃ r, freadGen E W ptr size n f s r := by
  by_cases h : (∃ st, (E).S.file s.m.memory f st) ∧
      s.m.memory.Permitted .write ptr.toNat (size.toNat * n.toNat) ∧
      s.m.memory.Permitted .read ptr.toNat (size.toNat * n.toNat) ∧
      (∀ a, ptr.toNat ≤ a → a < ptr.toNat + size.toNat * n.toNat → ¬ (E).S.priv s.m.memory a) ∧
      (E).S.lo ≤ (s.m.core.read .rsp).toNat
  · obtain ⟨⟨st, hst⟩, hwr, hrd, hx, hlo⟩ := h
    have hlo' : A0 + K0 * S0 ≤ (s.m.core.read .rsp).toNat := hlo
    have hs := hst.1
    have hsl := slot_lt hs
    have hsm := slot_small hs
    obtain ⟨hv', hle⟩ := readSt_valid hst.2.1 (size.toNat * n.toNat)
    have hdl := readSt_fst_length st (size.toNat * n.toNat)
    rcases hR : readSt st (size.toNat * n.toNat) with ⟨d, st'⟩
    rw [hR] at hv' hle hdl
    simp only at hv' hle hdl
    have hS' := hv'.2.2
    obtain ⟨pa, pw, pp⟩ := perm_of_read hst.2.2.1
    have hww := writable_of hwr
    unfold Memory.Permitted at hrd; rw [Memory.checkSpan_iff] at hrd
    obtain ⟨da, dw, dp⟩ := hrd
    simp only [Silmaril.Process.addressLimit] at da dw
    have hel : (enc st').length = 64 + st'.rd.length := enc_length st'
    let m1 := putBytes s.m.memory f.toNat (enc st')
    let m2 := putBytes m1 ptr.toNat d
    let t := retM s (BitVec.ofNat 64 (d.length / size.toNat)) m2 s.g
    -- what changed: `f`'s slot (private) and the destination
    have hkeep : ∀ x, (x < f.toNat ∨ f.toNat + S0 ≤ x) → (x < ptr.toNat ∨ ptr.toNat + d.length ≤ x) →
        m2.bytes.get? x = s.m.memory.bytes.get? x := by
      intro x h1 h2
      show (Memory.install (Memory.install s.m.memory.bytes f.toNat (enc st')) ptr.toNat d).get? x = _
      rw [Memory.install_outside _ _ _ _ h2, Memory.install_outside _ _ _ _ (by rw [hel]; omega)]
    have hfile : fileR m2 f st' := by
      refine ⟨hs, hv', ?_, fun k hk => hst.2.2.2 k (by omega)⟩
      have h1 : m1.readBytes f.toNat (64 + st'.rd.length) = some (enc st') := by
        rw [← hel]; exact read_put pa (by rw [hel]; omega) (fun k hk => pp k (by rw [hel] at hk; omega))
      rw [← h1]
      refine Keeps.readBytes (P := fun x => f.toNat ≤ x ∧ x < f.toNat + S0) ?_ (fun k hk => ⟨by omega, by omega⟩)
      intro x hx'
      refine ⟨Memory.install_outside _ _ _ _ ?_, fun _ => rfl⟩
      by_contra hc
      exact hx x (by omega) (by omega) ⟨by omega, by omega⟩
    have hdest : m2.readBytes ptr.toNat d.length = some d :=
      read_put da (by omega) (fun k hk => dp k (by omega))
    -- a stream other than `f` lies in its own slot, which the destination does not touch
    have hother : ∀ (f' : Word) (st'' : St), f' ≠ f → IsSlot f' → 64 + st''.rd.length ≤ S0 →
        (∀ k < 64 + st''.rd.length, s.m.memory.permits .write (f'.toNat + k) = false) →
        Keeps (fun x => f'.toNat ≤ x ∧ x < f'.toNat + (64 + st''.rd.length)) s.m.memory m2 := by
      intro f' st'' hne hs' hS'' hro x hx'
      refine ⟨hkeep x ?_ ?_, fun _ => rfl⟩
      · exact slot_disjoint hs hs' (Ne.symm hne) hx'.1 (by omega)
      · by_contra hc
        have h1 := hww (x - ptr.toNat) (by omega)
        have h2 := hro (x - f'.toNat) (by omega)
        rw [show ptr.toNat + (x - ptr.toNat) = x by omega] at h1
        rw [show f'.toNat + (x - f'.toNat) = x by omega, h1] at h2
        exact absurd h2 (by decide)
    refine ⟨.ok t, fun _ => ⟨t, rfl, fun st2 h2 => ?_⟩⟩
    obtain rfl := fileR_unique hst h2
    rw [hR]
    refine ⟨⟨⟨(retState_returns W s _ s.g).1, fun x hx' => ⟨?_, fun _ => rfl⟩⟩, rfl, fun _ _ _ _ => rfl,
      fun x hx' => ⟨?_, fun _ => rfl⟩, fun _ h => Or.inl h, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_⟩,
      rfl, ?_, hfile, hdest, retM_rax _ _ _ _⟩
    · apply hkeep
      · rcases hx'.1 with hk | hk
        · by_contra hc; exact hW x hk ⟨by omega, by omega⟩
        · right; omega
      · by_contra hc; exact hx'.2 ⟨by omega, by omega⟩
    · apply hkeep
      · by_contra hc; exact hx'.1 ⟨by omega, by omega⟩
      · by_contra hc; exact hx'.2.1 ⟨by omega, by omega⟩
    · intro f' st'' h''
      by_cases hne : f' = f
      · subst hne; exact Or.inl ⟨st, hst⟩
      · left
        refine ⟨st'', h''.1, h''.2.1, ?_, h''.2.2.2⟩
        rw [← (hother f' st'' hne h''.1 h''.2.1.2.2 h''.2.2.2).readBytes (fun k hk => ⟨by omega, by omega⟩)]
        exact h''.2.2.1
    · intro f' st'' hf' h''
      have hf2 : f' ≠ f := fun he => hf' (by simp [he])
      refine ⟨h''.1, h''.2.1, ?_, h''.2.2.2⟩
      show m2.readBytes _ _ = _
      rw [(hother f' st'' hf2 h''.1 h''.2.1.2.2 h''.2.2.2).readBytes (fun k hk => ⟨by omega, by omega⟩)]
      exact h''.2.2.1
  · exact ⟨.stop, fun hp => absurd ⟨hp.2.1, hp.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩ h⟩

theorem fread_ok (hW : ∀ a, W.Kept a → ¬ Arena a) : ∃ r, freadStep E W s r :=
  freadGen_ok fs optA W s hW _ _ _ _

theorem freadChk_ok (hW : ∀ a, W.Kept a → ¬ Arena a) : ∃ r, freadChkStep E W s r := by
  obtain ⟨r, hr⟩ := freadGen_ok fs optA W s hW (s.m.core.read .rdi) (s.m.core.read .rdx)
    (s.m.core.read .rcx) (s.m.core.read .r8)
  exact ⟨r, fun _ => hr⟩

/-- **`clearerr_unlocked` is total**: the stream's header is rewritten in its slot. -/
theorem clearerr_ok (hW : ∀ a, W.Kept a → ¬ Arena a) : ∃ r, clearerrStep E W s r := by
  by_cases h : (∃ st, (E).S.file s.m.memory (s.m.core.read .rdi) st) ∧ (E).S.lo ≤ (s.m.core.read .rsp).toNat
  · obtain ⟨⟨st, hst⟩, hlo⟩ := h
    have hlo' : A0 + K0 * S0 ≤ (s.m.core.read .rsp).toNat := hlo
    have hs := hst.1
    have hsl := slot_lt hs
    have hsm := slot_small hs
    let st' : St := { st with eof := false, err := false }
    have hv' : Valid st' := ⟨hst.2.1.1, hst.2.1.2.1, hst.2.1.2.2⟩
    have hel : (enc st').length = 64 + st.rd.length := enc_length st'
    obtain ⟨pa, pw, pp⟩ := perm_of_read hst.2.2.1
    let m1 := putBytes s.m.memory (s.m.core.read .rdi).toNat (enc st')
    have hkeep : ∀ x, (x < (s.m.core.read .rdi).toNat ∨ (s.m.core.read .rdi).toNat + S0 ≤ x) → m1.bytes.get? x = s.m.memory.bytes.get? x :=
      fun x hx => Memory.install_outside _ _ _ _ (by rw [hel]; have := hst.2.1.2.2; omega)
    have hfile : fileR m1 (s.m.core.read .rdi) st' := by
      refine ⟨hs, hv', ?_, fun k hk => hst.2.2.2 k hk⟩
      rw [show 64 + st'.rd.length = (enc st').length from hel.symm]
      exact read_put pa (by rw [hel]; omega) (fun k hk => pp k (by rw [hel] at hk; omega))
    have hother : ∀ (f' : Word) (st'' : St), f' ≠ s.m.core.read .rdi → fileR s.m.memory f' st'' ∨ fileR m1 f' st'' →
        ∀ x, f'.toNat ≤ x → x < f'.toNat + S0 →
          m1.bytes.get? x = s.m.memory.bytes.get? x ∧ ∀ acc, m1.permits acc x = s.m.memory.permits acc x := by
      intro f' st'' hne h x h1 h2
      have hs' : IsSlot f' := by rcases h with h | h <;> exact h.1
      exact ⟨hkeep x (slot_disjoint hs hs' (Ne.symm hne) h1 h2), fun _ => rfl⟩
    refine ⟨.ok (retM s 0#64 m1 s.g), fun _ => ⟨_, rfl, ⟨⟨(retState_returns W s 0#64 s.g).1,
      fun x hx => ⟨hkeep x ?_, fun _ => rfl⟩⟩, rfl, fun _ _ _ _ => rfl, fun x hx => ⟨hkeep x ?_, fun _ => rfl⟩,
      fun _ h => Or.inl h, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun f' st'' h'' => ?_⟩, rfl,
      fun f' st'' hf' h'' => ?_, fun st2 h2 => ?_⟩⟩
    · rcases hx.1 with hk | hk
      · by_contra hc; exact hW x hk ⟨by omega, by omega⟩
      · right; omega
    · by_contra hc; exact hx.1 ⟨by omega, by omega⟩
    · by_cases hne : f' = s.m.core.read .rdi
      · subst hne; exact Or.inl ⟨st, hst⟩
      · exact Or.inl ⟨st'', fileR_keep_slot h'' fun x h1 h2 => by
          have := hother f' st'' hne (Or.inr h'') x h1 h2; exact ⟨this.1.symm, fun acc => (this.2 acc).symm⟩⟩
    · have hf2 : f' ≠ s.m.core.read .rdi := fun he => hf' (by simp [he])
      exact fileR_keep_slot h'' (hother f' st'' hf2 (Or.inl h''))
    · obtain rfl := fileR_unique hst h2
      exact hfile
  · exact ⟨.stop, fun hp => absurd ⟨hp.2.1, hp.2.2⟩ h⟩

end

/-! ## `fopen` -/

theorem permits_add (m : Memory) (b : Silmaril.Process.ByteMemory) (r : Silmaril.Process.Region)
    (acc : Access) (a : Nat) (h : ¬ r.Contains a) :
    (Memory.mk (m.regions ++ [r]) b).permits acc a = m.permits acc a := by
  simp [Memory.permits, List.any_append, h]

theorem permits_rw (m : Memory) (b : Silmaril.Process.ByteMemory) (base n a : Nat) (h1 : base ≤ a)
    (h2 : a < base + n) :
    (Memory.mk (m.regions ++ [⟨base, n, ⟨true, true, false⟩⟩]) b).permits .read a = true := by
  simp [Memory.permits, List.any_append, Silmaril.Process.Region.Contains,
    Silmaril.Process.Permissions.allows]
  simp [h1, h2]

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word)
  (W : World) (s : PState)

local notation "E" => envOf fs optA

theorem openedSt_fd {r : Silmaril.Apps.Sha256sum.ReadResult} {st : St} (h : openedSt r 3 = some st) :
    st.fd = 3 ∧ st.buf = [] := by
  unfold openedSt at h; split at h <;> cases h <;> exact ⟨rfl, rfl⟩

theorem permits_rww (m : Memory) (b : Silmaril.Process.ByteMemory) (base n a : Nat) (h1 : base ≤ a)
    (h2 : a < base + n) :
    (Memory.mk (m.regions ++ [⟨base, n, ⟨true, true, false⟩⟩]) b).permits .write a = true := by
  simp [Memory.permits, List.any_append, Silmaril.Process.Region.Contains,
    Silmaril.Process.Permissions.allows]
  simp [h1, h2]

theorem permitted_new (m : Memory) (b : Silmaril.Process.ByteMemory) (base n : Nat) (acc : Access)
    (hacc : acc = .read ∨ acc = .write) (hn : base + n < 2 ^ 64) :
    (Memory.mk (m.regions ++ [⟨base, n, ⟨true, true, false⟩⟩]) b).Permitted acc base n := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rcases hacc with rfl | rfl
  · exact permits_rw _ _ _ _ _ (by omega) (by omega)
  · exact permits_rww _ _ _ _ _ (by omega) (by omega)

/-! ### Cutting a range out of the memory map -/

/-- The parts of a region below `lo` and from `hi` on. -/
def cutR (lo hi : Nat) (r : Silmaril.Process.Region) : List Silmaril.Process.Region :=
  [⟨r.base, min r.size (lo - r.base), r.permissions⟩, ⟨max r.base hi, r.base + r.size - max r.base hi, r.permissions⟩]

theorem any_cut (lo hi : Nat) (acc : Access) (a : Nat) (ha : a < lo ∨ hi ≤ a) :
    ∀ rs : List Silmaril.Process.Region,
      (rs.flatMap (cutR lo hi)).any (fun r => decide (r.Contains a) && r.permissions.allows acc) =
        rs.any (fun r => decide (r.Contains a) && r.permissions.allows acc)
  | [] => rfl
  | r :: rs => by
    rw [List.flatMap_cons, List.any_append, List.any_cons, any_cut lo hi acc a ha rs]
    congr 1
    simp only [cutR, List.any_cons, List.any_nil, Bool.or_false]
    cases r.permissions.allows acc
    · simp
    · simp only [Bool.and_true]
      rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
      unfold Silmaril.Process.Region.Contains
      dsimp only
      omega

theorem any_cut_in (lo hi : Nat) (acc : Access) (a : Nat) (h1 : lo ≤ a) (h2 : a < hi) :
    ∀ rs : List Silmaril.Process.Region,
      (rs.flatMap (cutR lo hi)).any (fun r => decide (r.Contains a) && r.permissions.allows acc) = false
  | [] => rfl
  | r :: rs => by
    rw [List.flatMap_cons, List.any_append, any_cut_in lo hi acc a h1 h2 rs, Bool.or_false]
    simp only [cutR, List.any_cons, List.any_nil, Bool.or_false]
    have e1 : ¬ (⟨r.base, min r.size (lo - r.base), r.permissions⟩ : Silmaril.Process.Region).Contains a := by
      unfold Silmaril.Process.Region.Contains; dsimp only; omega
    have e2 : ¬ (⟨max r.base hi, r.base + r.size - max r.base hi, r.permissions⟩ : Silmaril.Process.Region).Contains a := by
      unfold Silmaril.Process.Region.Contains; dsimp only; omega
    simp [e1, e2]

/-- The memory `m` with `[lo, hi)` replaced by a fresh region `nr` and bytes `b`. -/
def remap (m : Memory) (lo hi : Nat) (nr : Silmaril.Process.Region) (b : Silmaril.Process.ByteMemory) : Memory :=
  ⟨m.regions.flatMap (cutR lo hi) ++ [nr], b⟩

theorem remap_out (m : Memory) (lo hi : Nat) (nr : Silmaril.Process.Region) (b : Silmaril.Process.ByteMemory)
    (acc : Access) (a : Nat) (ha : a < lo ∨ hi ≤ a) (hn : ¬ nr.Contains a) :
    (remap m lo hi nr b).permits acc a = m.permits acc a := by
  unfold remap Memory.permits
  rw [List.any_append, any_cut lo hi acc a ha]
  simp [hn]

theorem remap_in (m : Memory) (lo hi : Nat) (nr : Silmaril.Process.Region) (b : Silmaril.Process.ByteMemory)
    (acc : Access) (a : Nat) (h1 : lo ≤ a) (h2 : a < hi) :
    (remap m lo hi nr b).permits acc a = (decide (nr.Contains a) && nr.permissions.allows acc) := by
  unfold remap Memory.permits
  rw [List.any_append, any_cut_in lo hi acc a h1 h2]
  simp

/-! ### `malloc` -/

theorem slot_hi {f : Word} (h : IsSlot f) : f.toNat + S0 ≤ A0 + KS * S0 := by
  obtain ⟨k, hk, he⟩ := h
  rw [he]
  have : k * S0 + S0 ≤ KS * S0 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  omega

theorem lo_eq (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word) :
    (envOf fs optA).S.lo = A0 + K0 * S0 := rfl

/-- The library state after `malloc` returned the block at `a`. -/
def ghA (s : PState) (a : Nat) : Ghost :=
  { s.g with
    allocs := s.g.allocs + 1
    heap := s.g.heap + (s.m.core.read .rdi).toNat
    blocks := (a, (s.m.core.read .rdi).toNat) :: s.g.blocks }

/-- **`malloc` has an outcome** given room: when `AllocRoom` holds, an unmapped range more than
1 MiB below the arena, outside the kept memory, for the block. -/
theorem malloc_total
    (hspace : AllocRoom E s → ∃ a, 0 < a ∧ a + (s.m.core.read .rdi).toNat + 0x100000 ≤ A0 ∧
      ∀ x, a ≤ x → x < a + (s.m.core.read .rdi).toNat → s.m.memory.permits .read x = false ∧ ¬ W.Kept x) :
    ∃ r, mallocStep E W s r := by
  by_cases hR : AllocRoom E s
  · obtain ⟨a, ha0, haA, hfree⟩ := hspace hR
    have hrsp : A0 + K0 * S0 ≤ (s.m.core.read .rsp).toNat := hR.2.1
    have hA : A0 < 2 ^ 32 := by unfold A0; decide
    let n := (s.m.core.read .rdi).toNat
    let m' : Memory := ⟨s.m.memory.regions ++ [⟨a, n, ⟨true, true, false⟩⟩], s.m.memory.bytes⟩
    have hout : ∀ x, (x < a ∨ a + n ≤ x) → ∀ acc, m'.permits acc x = s.m.memory.permits acc x :=
      fun x hx acc => permits_add _ _ _ acc x (by simp [Silmaril.Process.Region.Contains]; omega)
    have ha64 : (BitVec.ofNat 64 a).toNat = a := by simp; unfold A0 at haA; omega
    have hslot : ∀ f st, fileR s.m.memory f st ∨ fileR m' f st → ∀ x, f.toNat ≤ x → x < f.toNat + S0 →
        m'.bytes.get? x = s.m.memory.bytes.get? x ∧ ∀ acc, m'.permits acc x = s.m.memory.permits acc x := by
      intro f st h x h1 h2
      have hs : IsSlot f := by rcases h with h | h <;> exact h.1
      have := slot_lt hs
      exact ⟨rfl, hout x (Or.inr (by omega))⟩
    let t := retM s (BitVec.ofNat 64 a) m' (ghA s a)
    have hrx : t.m.core.read .rax = BitVec.ofNat 64 a := retM_rax _ _ _ _
    refine ⟨.ok t, fun _ => ⟨t, rfl, ⟨⟨(retState_returns W s (BitVec.ofNat 64 a) (ghA s a)).1, fun x hx => ⟨rfl, hout x ?_⟩⟩, rfl,
      fun x h1 h2 acc => hout x (Or.inr (by omega)) acc, fun x hx => ⟨rfl, hout x ?_⟩, fun _ h => Or.inl h,
      fun x _ hr acc => hout x ?_ acc, fun x hx _ _ acc => hout x ?_ acc, fun f st h => ?_⟩, rfl,
      fun f st _ h => ?_, Or.inr ⟨?_, rfl, rfl, by rw [hrx, ha64]; rfl, ?_, ?_, fun x h1 h2 => ?_⟩⟩⟩
    · rcases hx.1 with hk | hk
      · by_contra hc; exact (hfree x (by omega) (by omega)).2 hk
      · right; omega
    · by_contra hc; have := (hfree x (by omega) (by omega)).1
      exact absurd (show s.m.memory.permits .read x = true from hx.2.2) (by rw [this]; simp)
    · by_contra hc; have := (hfree x (by omega) (by omega)).1; rw [this] at hr; exact absurd hr (by simp)
    · by_contra hc; apply hx; show (BitVec.ofNat 64 a) ≠ 0#64 ∧ _
      refine ⟨fun h0 => by have := congrArg BitVec.toNat h0; rw [ha64] at this; simp at this; omega, ?_, ?_⟩ <;>
        rw [hrx, ha64] <;> omega
    · exact Or.inl ⟨st, fileR_keep_slot h fun x h1 h2 => by
        have := hslot f st (Or.inr h) x h1 h2; exact ⟨this.1.symm, fun acc => (this.2 acc).symm⟩⟩
    · exact fileR_keep_slot h (hslot f st (Or.inl h))
    · rw [hrx]; intro h0
      have := congrArg BitVec.toNat h0
      rw [ha64] at this; simp at this; omega
    · rw [hrx, ha64]; exact permitted_new _ _ _ _ _ (Or.inl rfl) (by unfold A0 at haA; omega)
    · rw [hrx, ha64]; exact permitted_new _ _ _ _ _ (Or.inr rfl) (by unfold A0 at haA; omega)
    · rw [hrx, ha64] at h1 h2
      obtain ⟨hr0, hk0⟩ := hfree x h1 h2
      exact ⟨fun hp => by obtain ⟨hp1, -⟩ := hp; omega, hk0, by omega, by show x < A0 + K0 * S0; omega,
        Or.inr hr0⟩
  · refine ⟨.ok (retM s 0#64 s.m.memory s.g), fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _, rfl,
      others_same _ _ _ _ _, Or.inl ⟨retM_rax _ _ _ _, Or.inr hR, rfl, rfl, rfl⟩⟩⟩

/-! ### `fopen` -/

theorem fopen_total (hW : ∀ a, W.Kept a → ¬ Arena a)
    (hfs : ∀ p e, (E).fs p ≠ .openErr e)
    (hslot : ∀ st, OpenRoom E s st → ∃ k < KS, ∀ st0, ¬ fileR s.m.memory (BitVec.ofNat 64 (A0 + k * S0)) st0) :
    ∃ r, fopenStep E W s r := by
  by_cases h : ∃ p, CStr s.m.memory (s.m.core.read .rdi) p
  · obtain ⟨p, hp⟩ := h
    rcases ho : openedSt ((E).fs (toSpec p)) 3 with _ | st
    · exfalso
      revert ho; cases he : (E).fs (toSpec p) with
      | ok d => simp [openedSt]
      | readErr e pre => simp [openedSt]
      | openErr e => exact absurd he (hfs _ e)
    by_cases hR : OpenRoom E s st
    · obtain ⟨k, hk, hfree⟩ := hslot st hR
      have hrsp : A0 + K0 * S0 ≤ (s.m.core.read .rsp).toNat := hR.2.1
      obtain ⟨hfd, hbuf⟩ := openedSt_fd ho
      have hS : 64 + st.rd.length ≤ S0 := by
        have h1 : st.rd.length ≤ S0 - 64 := hR.2.2.2
        have : 64 ≤ S0 := by decide
        omega
      let f : Word := BitVec.ofNat 64 (A0 + k * S0)
      have hfn : f.toNat = A0 + k * S0 := by
        simp only [f, BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        have : k * S0 < KS * S0 := Nat.mul_lt_mul_of_pos_right hk (by decide)
        unfold A0 KS S0 at *; omega
      have hs : IsSlot f := ⟨k, hk, hfn⟩
      have hsl := slot_lt hs
      have hsh := slot_hi hs
      have hS0 : S0 = 0x100000 := rfl
      have hsh' : f.toNat + 0x100000 ≤ 0x10000000 + 15 * 0x100000 := by unfold KS S0 A0 at hsh; omega
      have hrsp' : 0x10000000 + 16 * 0x100000 ≤ (s.m.core.read .rsp).toNat := by unfold A0 K0 S0 at hrsp; omega
      have hf0 : f ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0; rw [hfn] at this; unfold A0 at this; simp at this
      have hv : Valid st := ⟨hbuf, by rw [hfd]; decide, hS⟩
      have hel := enc_length st
      let nr : Silmaril.Process.Region := ⟨f.toNat, S0, ⟨true, false, false⟩⟩
      let m' : Memory := remap s.m.memory f.toNat (f.toNat + S0) nr (Memory.install s.m.memory.bytes f.toNat (enc st))
      have hout : ∀ x, (x < f.toNat ∨ f.toNat + S0 ≤ x) →
          m'.bytes.get? x = s.m.memory.bytes.get? x ∧ ∀ acc, m'.permits acc x = s.m.memory.permits acc x :=
        fun x hx => ⟨Memory.install_outside _ _ _ _ (by rw [hel]; omega),
          fun acc => remap_out _ _ _ _ _ acc x hx (by simp [nr, Silmaril.Process.Region.Contains]; omega)⟩
      have hin : ∀ x acc, f.toNat ≤ x → x < f.toNat + S0 → m'.permits acc x = nr.permissions.allows acc := by
        intro x acc h1 h2
        rw [remap_in _ _ _ _ _ acc x h1 h2]
        simp [nr, Silmaril.Process.Region.Contains, h1, h2]
      have hfile : fileR m' f st := by
        refine ⟨hs, hv, ?_, fun j hj => by rw [hin _ _ (by omega) (by omega)]; rfl⟩
        rw [← hel]
        have := readWith_of_points (mem := m') (acc := .read) (l := enc st) (a := f.toNat)
          (by have := slot_small hs; omega) (by have := slot_small hs; omega)
          (fun j hj => ⟨by rw [hin _ _ (by omega) (by rw [hel] at hj; omega)]; rfl, Memory.install_get _ _ _ _ hj⟩)
        simpa [Memory.readBytes] using this
      have hother : ∀ f' st', f' ≠ f → fileR s.m.memory f' st' ∨ fileR m' f' st' →
          ∀ x, f'.toNat ≤ x → x < f'.toNat + S0 →
            m'.bytes.get? x = s.m.memory.bytes.get? x ∧ ∀ acc, m'.permits acc x = s.m.memory.permits acc x := by
        intro f' st' hne h x h1 h2
        have hs' : IsSlot f' := by rcases h with h | h <;> exact h.1
        exact hout x (slot_disjoint hs hs' (Ne.symm hne) h1 h2)
      let t := retM s f m' { s.g with files := s.g.files + 1 }
      have hrax : t.m.core.read .rax = f := retM_rax _ _ _ _
      refine ⟨.ok t, fun _ => ⟨t, rfl, ⟨⟨(retState_returns W s f { s.g with files := s.g.files + 1 }).1, fun x hx => ?_⟩, rfl,
        fun x h1 h2 acc => ?_, fun x hx => ?_, fun _ h => Or.inl h, fun x hx _ acc => ?_,
        fun x _ _ hx acc => ?_, fun f' st' h' => ?_⟩, rfl, fun f' st' _ h' => ?_, fun p' hp' => ?_⟩⟩
      · apply hout
        rcases hx.1 with hk' | hk'
        · by_contra hc; exact hW x hk' ⟨by omega, by omega⟩
        · right; omega
      · exact (hout x (Or.inr (by omega))).2 acc
      · apply hout
        by_contra hc; exact hx.1 ⟨by omega, by omega⟩
      · refine (hout x ?_).2 acc
        by_contra hc; exact hx ⟨by omega, by omega⟩
      · refine (hout x ?_).2 acc
        by_contra hc; exact hx ⟨by omega, by omega⟩
      · by_cases hne : f' = f
        · subst hne
          exact Or.inr fun a ha => ⟨by rw [hrax]; exact hf0, by rw [hrax]; exact ha⟩
        · exact Or.inl ⟨st', fileR_keep_slot h' fun x h1 h2 => by
            have := hother f' st' hne (Or.inr h') x h1 h2; exact ⟨this.1.symm, fun acc => (this.2 acc).symm⟩⟩
      · have hne : f' ≠ f := fun he => hfree st' (by subst he; exact h')
        exact fileR_keep_slot h' (hother f' st' hne (Or.inl h'))
      · obtain rfl := cstr_unique hp hp'
        rw [ho]
        have hst : { st with fd := 3 } = st := by rw [← hfd]
        refine Or.inr ⟨3, ?_, ?_, le_refl _, by decide, rfl, fun a ha => ?_, fun st0 h0 => ?_⟩
        · rw [hst, hrax]; exact hfile
        · rw [hrax]; exact hf0
        · rw [hrax] at ha
          have hin' := foot_in_slot hfile ha
          refine ⟨fun hk' => hW a hk' ⟨by omega, by omega⟩, ?_, Or.inl ⟨by omega, by omega⟩⟩
          unfold KS K0 S0 at *; omega
        · rw [hrax] at h0; exact hfree st0 h0
    · refine ⟨.ok (retM s 0#64 s.m.memory s.g), fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _, rfl,
        others_same _ _ _ _ _, fun p' hp' => ?_⟩⟩
      obtain rfl := cstr_unique hp hp'
      rw [ho]
      exact Or.inl ⟨retM_rax _ _ _ _, Or.inr hR, rfl⟩
  · exact ⟨.stop, fun hp => absurd hp.2.1 h⟩

end

/-! ## The two proposed contracts (`Streams.Extra`) -/

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (optA : Word)
  (W : World) (s : PState)

local notation "E" => envOf fs optA

theorem strcspn_ok : ∃ r, strcspnStep E W s r := by
  by_cases h : (∃ a, CStr s.m.memory (s.m.core.read .rdi) a) ∧ ∃ b, CStr s.m.memory (s.m.core.read .rsi) b
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    refine ⟨.ok (retM s (BitVec.ofNat 64 (a.takeWhile (fun c => !b.contains c)).length) s.m.memory s.g),
      fun _ => ⟨_, rfl, libRet0 fs optA W s _ _ _, rfl, others_same _ _ _ _ _, fun a' b' ha' hb' => ?_⟩⟩
    obtain rfl := cstr_unique ha ha'
    obtain rfl := cstr_unique hb hb'
    exact retM_rax _ _ _ _
  · exact ⟨.stop, fun hp => absurd hp.2 h⟩

theorem fputs_ok : ∃ r, fputsStep E W s r := by
  by_cases h : ∃ str, CStr s.m.memory (s.m.core.read .rdi) str
  · obtain ⟨str, hs⟩ := h
    refine ⟨.ok (retM s 0#64 s.m.memory (outG s str)), fun _ => ⟨_, rfl,
      libRet0 fs optA W s _ _ _, ghostOut s _ _, others_same _ _ _ _ _, fun str' h' => ?_⟩⟩
    obtain rfl := cstr_unique hs h'
    exact ⟨appended_same fs optA W s _ _ _ rfl, fun _ => by rw [retM_rax]; decide⟩
  · exact ⟨.stop, fun hp => absurd hp.2.2.2 h⟩

end

end Silmaril.Elf.Link.Dyn.Streams.Total
