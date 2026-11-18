module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitLoad
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinLaws
public import Silmaril.Raw.Elf.Link.Dyn.Streams.Total

/-! # GNU `sha256sum`: a concrete world with every import contract (non-vacuity, part 2)

`Wof fs A`: the process world of the concrete loaded `sha256sum` (`WitLoad`), with eager binding, the
gate inside libc, reliable output, the argument area above `argc` on the kernel's stack, the TCB's
guard and libc's stream variables as kept library memory, and **every import of the stdin and
file tiers bound to its contract** through one table (`table0`, `Proc.Witness.namedOf`). The
library's guarantee at `main` is a parameter `A`; the exit guarantees are those `ExitOk` asks
(`atCall`: the callback stack above the arena; `atGate`: streams kept).

Proved for it: `ShaWorldOk`, `MainImps`, `TailImps` (with `StdinImps`, `DigImps`, `CloseImps`,
`PrintImps` and the stream laws of `slot_tailLaws`) and `ExitOk`, for the environment
`Streams.Total.envOf fs (lb0 + 0x204248)` (the slot representation, `allocOk = true`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total
open Silmaril.Elf.Link.Dyn.Imports

/-- Where callbacks return to (inside libc). -/
def gate0 : Word := lb0 + 0x29d90#64
/-- The `strrchr` and `strcspn` implementations (`ifn0` resolves an ifunc to itself). -/
def sr0 : Word := lb0 + 0xb5210#64
def sc0 : Word := lb0 + 0xb4410#64

theorem gate0_toNat : gate0.toNat = 0x7ffff7c29d90 := by decide
theorem gate_lsm0 : gate0 ≠ lb0 + 0x2a200#64 := by decide +kernel
theorem gate_cxa0 : gate0 ≠ lb0 + 0x472c0#64 := by decide +kernel
theorem cxa_ne0 : lb0 + 0x472c0#64 ≠ 0#64 := by decide +kernel
theorem out_ne0 : outF ≠ errF := by decide +kernel

/-- The argument area: above `argc`, in the kernel's stack pages. -/
def args0 (a : Nat) : Prop := sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 4096
/-- Kept library memory: the guard at `fs0 + 0x28`, libc's `stderr`/`stdout`/`stdin`. -/
def tls0 (a : Nat) : Prop :=
  (fs0.toNat + 0x28 ≤ a ∧ a < fs0.toNat + 0x30) ∨ (lb0.toNat + 0x2056a0 ≤ a ∧ a < lb0.toNat + 0x2056b8)

/-- The environment: the slot representation, `optind` in libc's `.data`. -/
def E0 (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) : Env :=
  envOf fs (lb0 + 0x204248#64)

/-- The imports bound by address. -/
def fns0 : List (Word × Fn) :=
  [(lb0 + 0x2a200#64, .libcStartMain), (lb0 + 0x472c0#64, .cxaFinalize),
   (sr0, .named (nm "strrchr")), (lb0 + 0x3a6b0#64, .named (nm "setlocale")),
   (lb0 + 0x3bf00#64, .named (nm "bindtextdomain")), (lb0 + 0x406f0#64, .named (nm "textdomain")),
   (lb0 + 0x471f0#64, .named (nm "__cxa_atexit")), (lb0 + 0x88630#64, .named (nm "setvbuf")),
   (lb0 + 0xf5ad0#64, .named (nm "getopt_long")), (lb0 + 0x91400#64, .named (nm "clearerr_unlocked")),
   (lb0 + 0x11b2a0#64, .named (nm "lseek")), (lb0 + 0x85f40#64, .named (nm "fopen")),
   (lb0 + 0x11b7f0#64, .named (nm "posix_fadvise")), (lb0 + 0xad750#64, .named (nm "malloc")),
   (lb0 + 0xade30#64, .named (nm "free")), (lb0 + 0x137130#64, .named (nm "__fread_unlocked_chk")),
   (kb0 + 0x33d3c0#64, .named (nm "SHA256_Init")), (kb0 + 0x33d410#64, .named (nm "SHA256_Update")),
   (kb0 + 0x33d630#64, .named (nm "SHA256_Final")), (lb0 + 0x8ea80#64, .named (nm "fileno")),
   (lb0 + 0x90790#64, .named (nm "__freading")), (lb0 + 0x858d0#64, .named (nm "fflush")),
   (lb0 + 0x85370#64, .named (nm "fclose")), (lb0 + 0x90880#64, .named (nm "__fpending")),
   (lb0 + 0x137bf0#64, .named (nm "__printf_chk")), (lb0 + 0x95120#64, .named (nm "__overflow")),
   (lb0 + 0x91890#64, .named (nm "fputs_unlocked")), (sc0, .named (nm "strcspn"))]

theorem lsm0 : fns0.find? (·.1 == lb0 + 0x2a200#64) = some (lb0 + 0x2a200#64, .libcStartMain) := by decide +kernel
theorem cxa0 : fns0.find? (·.1 == lb0 + 0x472c0#64) = some (lb0 + 0x472c0#64, .cxaFinalize) := by decide +kernel

/-- The world without its contracts and `main` guarantee (the frame the contracts refer to). -/
def Wf : World where
  base := b0
  size := 0xa188
  inits := [b0 + 0x2000#64, b0 + 0x3b20#64]
  finis := [b0 + 0x3ae0#64, b0 + 0x6d44#64]
  gate := gate0
  lazy := none
  fns := fns0
  reliable := true
  args := args0
  tls := tls0
  atCall t := slotRep.lo + 1024 ≤ (t.m.core.read .rsp).toNat
  atGate s t := ∀ f st, fileR s.m.memory f st → fileR t.m.memory f st

/-- The contract table of `sha256sum`'s imports. -/
def table0 (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) : Table :=
  let E := E0 fs
  let W := Wf
  [(nm "strrchr", strrchrStep E W),
   (nm "setlocale", framed E W (fun _ _ => False) (quietStep W fun _ => True)),
   (nm "bindtextdomain", framed E W (fun _ _ => False) (quietStep W fun _ => True)),
   (nm "textdomain", framed E W (fun _ _ => False) (quietStep W fun _ => True)),
   (nm "__cxa_atexit", framed E W (fun _ _ => False) (cxaAtexitFirst W)),
   (nm "setvbuf", setvbufStep E W), (nm "getopt_long", getoptNoneStep E W),
   (nm "clearerr_unlocked", clearerrStep E W), (nm "lseek", lseekStep E W), (nm "fopen", fopenStep E W),
   (nm "posix_fadvise", fadviseStep E W), (nm "malloc", mallocStep E W), (nm "free", freeStep E W),
   (nm "__fread_unlocked_chk", freadChkStep E W),
   (nm "SHA256_Init", framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256InitStep shaRep W)),
   (nm "SHA256_Update", framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256UpdateStep shaRep W)),
   (nm "SHA256_Final", framed E W (fun s a => ctxRange (s.m.core.read .rsi) a ∨
      ((s.m.core.read .rdi).toNat ≤ a ∧ a < (s.m.core.read .rdi).toNat + 32)) (sha256FinalStep shaRep W)),
   (nm "fileno", filenoStep E W), (nm "__freading", freadingStep E W), (nm "fflush", fflushStep E W),
   (nm "fclose", fcloseStep E W), (nm "__fpending", fpendingStep E W),
   (nm "__printf_chk", printfHexStep E W), (nm "__overflow", overflowStep E W),
   (nm "fputs_unlocked", fputsStep E W), (nm "strcspn", strcspnStep E W)]

/-- **The world**, with the library's guarantee `A` at `main`. -/
def Wof (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop) : World :=
  { Wf with named := Witness.namedOf (table0 fs), atMain := A }

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop)

theorem wof_inImage : (Wof fs A).InImage = ShaImg b0 := rfl
theorem wof_kept (a : Nat) : (Wof fs A).Kept a ↔ ShaImg b0 a ∨ args0 a ∨ tls0 a := Iff.rfl

theorem hb0 : b0.toNat + 0xa188 < 2 ^ 64 := by rw [b0_toNat]; decide

theorem out_img {a : Word} (h : 0x555555554000 + 0xa188 ≤ a.toNat) : ¬ (Wof fs A).InImage a.toNat := by
  rw [wof_inImage]; simp only [ShaImg, b0_toNat]; omega

/-- `ImpOk` of a table entry of `Wof`. -/
theorem impOk0 {a : Word} {n : Name} {c : PState → Res PState → Prop}
    (hout : 0x555555554000 + 0xa188 ≤ a.toNat) (hg : a ≠ gate0)
    (hf : fns0.find? (·.1 == a) = some (a, .named n)) (ht : (table0 fs).find? (·.1 == n) = some (n, c)) :
    ImpOk (Wof fs A) a n c :=
  ⟨out_img fs A hout, hg, hf, Witness.namedOf_eq ht⟩

theorem lb0_add (k : Nat) (hk : k < 2 ^ 32) : (lb0 + BitVec.ofNat 64 k).toNat = 0x7ffff7c00000 + k :=
  addr_toNat (by rw [lb0_toNat]; omega)

theorem kb0_add (k : Nat) (hk : k < 2 ^ 32) : (kb0 + BitVec.ofNat 64 k).toNat = 0x7ffff7400000 + k :=
  addr_toNat (by rw [kb0_toNat]; omega)

theorem worldOk : ShaWorldOk (Wof fs A) b0 lb0 :=
  ⟨rfl, hb0, rfl, rfl, rfl, lsm0, by simp only [ShaImg, b0_toNat]; rw [lb0_add _ (by decide)]; omega,
    by show ¬ ShaImg b0 gate0.toNat; rw [gate0_toNat]; simp only [ShaImg, b0_toNat]; omega, gate_lsm0⟩
end

section
variable (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop)

local macro "imp" : term => `(impOk0 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl)

theorem mainImps0 : MainImps (E0 fs) (Wof fs A) b0 lb0 sr0 :=
  ⟨rfl, rfl, hb0, imp, ⟨imp, imp, imp⟩, imp, imp, imp⟩

theorem closeImps0 : CloseImps (E0 fs) (Wof fs A) b0 lb0 :=
  ⟨rfl, rfl, hb0, imp, imp, imp, imp, imp⟩

theorem digImps0 : DigImps (E0 fs) shaRep (Wof fs A) b0 lb0 kb0 :=
  ⟨closeImps0 fs A, imp, imp, imp, imp, imp, imp, imp, imp, imp, rfl⟩

theorem printImps0 : PrintImps (E0 fs) (Wof fs A) b0 lb0 sc0 :=
  ⟨rfl, rfl, hb0, imp, imp, imp, imp⟩

theorem slot0 : IsSlot (E0 fs).stdoutF := ⟨0, by decide, by simp [E0, envOf, A0]⟩

theorem kept_arena (a : Nat) (h : (Wof fs A).Kept a) : ¬ Arena a := by
  rw [wof_kept] at h
  simp only [Arena, A0, K0, S0, ShaImg, args0, tls0, b0_toNat, sp0_toNat, fs0_toNat, lb0_toNat] at h ⊢
  omega

theorem tailImps0 : TailImps (E0 fs) shaRep (Wof fs A) b0 lb0 kb0 sc0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := slot_tailLaws (E0 fs) rfl (slot0 fs) out_ne0 (Wof fs A) (kept_arena fs A)
  exact ⟨⟨digImps0 fs A, imp⟩, printImps0 fs A, h1, h2, h3, h4, h5, rfl, rfl, h6⟩

theorem exitOk0 : ExitOk (E0 fs) (Wof fs A) b0 lb0 :=
  ⟨closeImps0 fs A, worldOk fs A, cxa0,
    by simp only [ShaImg, b0_toNat]; rw [lb0_add _ (by decide)]; omega, gate_cxa0, cxa_ne0, rfl,
    fun h => out_ne0 h.symm, fun _ h => h, fun _ _ f st h hf => h f st hf, fun _ _ h => h⟩

end

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
