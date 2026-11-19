module

public import Silmaril.Sim.GlibcBridge.Elf.Defs
public import Silmaril.Proofs.Sim.GlibcBridge.BytesConv
public import Silmaril.Sim.GlibcBridge.Link.Thms
public import Silmaril.Sim.GlibcBridge.Start.Defs

/-!
# The pinned ELF under the eager loader: GOT word, code bytes, string

* `exe_rels`, `exe_plt`, `exe_main`, `exe_msg`, `exe_undef_puts`: what the loader model reads
  from the pinned file (`decide +kernel`).
* **`got_puts`**: under `EagerLoaded ghelloLinkMap`, `GOT[puts]` holds `putsF` (`got_word`).
* `plt_loaded`, `main_loaded`: the code bytes are fetchable; `cstr_msg`: the string is
  readable as a C string.
* **`ghello_e2e`** / **`ghello_e2e_impl`**: the end-to-end statement; its hypotheses are exactly
  what remains trusted (see the docstring).
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Sim.GlibcBridge.Link
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS.Machines (viewByte)

theorem exe_rels : exeObj.rels =
    [⟨0x403fd8, 6, nm "__libc_start_main", false, 0⟩, ⟨0x403fe0, 6, nm "__gmon_start__", true, 0⟩,
     ⟨0x404000, 7, nm "puts", false, 0⟩] := by decide +kernel

theorem exe_plt : exeObj.slice 0x401040 10 = some (pltBytes, 5) := by decide +kernel

theorem exe_main : exeObj.slice 0x401050 27 = some (mainBytes, 5) := by decide +kernel

theorem exe_msg : exeObj.slice 0x402004 14 = some (msgS ++ [0], 4) := by decide +kernel

theorem exe_undef_puts : exeObj.defines (nm "puts") = none := by decide +kernel

theorem subset_puts : subsetObj.defines (nm "puts") = some ⟨0, false⟩ := by decide

variable {ifn : Word → Option Word} {mem : Memory}

/-- **`GOT[puts]` after eager binding** is the foreign address of `puts`. -/
theorem got_puts (hL : EagerLoaded ghelloLinkMap ifn mem) :
    Silmaril.X86.Ext.loadN mem gotPuts 8 = some putsF := by
  obtain ⟨g, hg, hload⟩ := got_word hL (List.mem_cons_self ..)
    (r := ⟨0x404000, 7, nm "puts", false, 0⟩) (by rw [exe_rels]; simp) (.inr rfl) rfl
  have hres : resolveIn ifn ghelloLinkMap (nm "puts") = some putsF := by
    simp [ghelloLinkMap, resolveIn, exe_undef_puts, subset_puts, putsF, extBase]
  rw [hres] at hg
  cases hg
  simpa [gotPuts] using hload

theorem plt_loaded (hL : EagerLoaded ghelloLinkMap ifn mem) :
    mem.fetchBytes 0x401040 pltBytes.length = some pltBytes := by
  have := (hL.image _ (List.mem_cons_self ..)).code 0x401040 10 pltBytes 5 exe_plt (by decide)
  simpa [Silmaril.X86.Ext.Loaded] using this

theorem main_loaded (hL : EagerLoaded ghelloLinkMap ifn mem) :
    mem.fetchBytes 0x401050 mainBytes.length = some mainBytes := by
  have := (hL.image _ (List.mem_cons_self ..)).code 0x401050 27 mainBytes 5 exe_main (by decide)
  simpa [Silmaril.X86.Ext.Loaded] using this

theorem msg_read (hL : EagerLoaded ghelloLinkMap ifn mem) :
    mem.readBytes 0x402004 14 = some (msgS ++ [0]) := by
  have := (hL.image _ (List.mem_cons_self ..)).rodata 0x402004 14 _ 4 exe_msg (by decide)
  simpa using this

/-! ## C strings from reads -/

theorem viewByte_of_read {a n : Nat} {bs : List Byte} (h : mem.readBytes a n = some bs) {i : Nat}
    (hi : i < bs.length) : viewByte mem .read (BitVec.ofNat 64 (a + i)) = some bs[i] := by
  have hn := Silmaril.Process.Memory.readWith_length h
  have hp := Silmaril.Process.Memory.readWith_permitted h
  rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at hp
  have hb := hp.2.1
  have hg := Silmaril.Process.Memory.readWith_get h i hi
  have ht : (BitVec.ofNat 64 (a + i)).toNat = a + i := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    simp only [Silmaril.Process.addressLimit] at hb; omega
  simp only [viewByte, ht, hp.2.2 i (by omega), ite_true]
  rw [← Std.ExtHashMap.get?_eq_getElem?]
  exact hg

theorem cstrAux_of {rd : Word → Option Byte} :
    ∀ (s : List Byte) (p : Word) (k : Nat),
      (∀ i (hi : i < s.length), rd (p + BitVec.ofNat 64 i) = some s[i]) →
      rd (p + BitVec.ofNat 64 s.length) = some 0 → (∀ b ∈ s, b ≠ 0) →
      cstrAux rd p (s.length + k + 1) = some s
  | [], p, k, _, h0, _ => by
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    simp [cstrAux, h0]
  | b :: s, p, k, hs, h0, hnz => by
    have hb : rd p = some b := by
      have := hs 0 (by simp)
      rwa [List.getElem_cons_zero, show p + BitVec.ofNat 64 0 = p by bv_omega] at this
    have ih := cstrAux_of (rd := rd) s (p + 1) k
      (fun i hi => by
        have := hs (i + 1) (by simp; omega)
        rwa [List.getElem_cons_succ,
          show p + BitVec.ofNat 64 (i + 1) = p + 1 + BitVec.ofNat 64 i by bv_omega] at this)
      (by
        rwa [List.length_cons,
          show p + BitVec.ofNat 64 (s.length + 1) = p + 1 + BitVec.ofNat 64 s.length by bv_omega] at h0)
      (fun c hc => hnz c (List.mem_cons_of_mem _ hc))
    have hb0 : b ≠ 0 := hnz b (List.mem_cons_self ..)
    rw [show (b :: s).length + k + 1 = (s.length + k + 1) + 1 by simp; omega]
    rw [cstrAux]
    simp only [hb, hb0, ite_false, ih, Option.map_some]

/-- **The string** at `0x402004` is `"Hello, world!"`. -/
theorem cstr_msg (hL : EagerLoaded ghelloLinkMap ifn mem) : cstr mem ghMsg = some msgS := by
  have hr := msg_read hL
  have hv : ∀ i (hi : i < (msgS ++ [0]).length),
      viewByte mem .read (ghMsg + BitVec.ofNat 64 i) = some (msgS ++ [0])[i] := by
    intro i hi
    have := viewByte_of_read hr hi
    rwa [show BitVec.ofNat 64 (0x402004 + i) = ghMsg + BitVec.ofNat 64 i by
      simp [ghMsg, BitVec.ofNat_add]] at this
  have h := cstrAux_of (rd := viewByte mem .read) msgS ghMsg (65536 - 14)
    (fun i hi => by
      have := hv i (by simp at hi ⊢; omega)
      rwa [List.getElem_append_left hi] at this)
    (by
      have := hv 13 (by decide)
      rw [show msgS.length = 13 by decide]
      rw [show (msgS ++ [0])[13] = 0 by decide] at this
      exact this)
    (by decide)
  rw [show msgS.length + (65536 - 14) + 1 = 65536 by decide] at h
  exact h

/-! ## End to end -/

/-- **The glibc-linked hello, end to end.** Trusted, as hypotheses: the eager-binding loader
relation for the bridge's link map (`EagerLoaded ghelloLinkMap`, what `loader-glibc.wat` does;
the file is `exe` by its sha256), the guest-load import answering by memory (`hld`), the start-up
contract (`StartAtMain`), and the `puts` implementation (`Meets P putsC1`, admitting each output).
Everything else is proved: the code table is the loaded bytes, `GOT[puts]` is the import's
address, the string is the C string, and the dispatcher runs of GM on the actual instructions
are equivalent to the WASI hello. -/
theorem ghello_e2e {ifn : Word → Option Word} (hL : EagerLoaded ghelloLinkMap ifn mem)
    {ld : Word → Option Word} (hld : ∀ a, ld a = Silmaril.X86.Ext.loadN mem a 8)
    {P : ImportC} (hP : Meets P putsC1)
    (hA : ∀ args k, args.head? = some ghMsg → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((Silmaril.Sim.WasiBridge.G.helloMsg.take k).map (.wr 1)) (some v))
    {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H} {f : Silmaril.Wasm.Execution.Core.Frame}
    {W : Silmaril.Sim.X86.GM.Win} {σ : Silmaril.X86.State} (hS : StartAtMain s f mem W σ) :
    TabAt mem ghelloTab ∧
      Silmaril.Sim.WasiBridge.ElfWasiEquiv (blinkObs (ghelloC P) mem W ld ghelloFm ghelloTab s f)
        Silmaril.Sim.WasiBridge.G.helloWasi Silmaril.Sim.WasiBridge.S1 :=
  ⟨tabAt_ghello (plt_loaded hL) (main_loaded hL),
    ghelloB_equiv hP hA (cstr_msg hL) (by rw [hld]; exact got_puts hL) hS.enc hS.memEnc hS.rw hS.rip
      hS.ret hS.win0 hS.win16 hS.low⟩

/-- **End to end with `glibc.wat`'s `puts`** (its behaviour `putsImpl`; the Wasm code of
`glibc.wat` against `putsImpl` is not proved). -/
theorem ghello_e2e_impl {ifn : Word → Option Word} (hL : EagerLoaded ghelloLinkMap ifn mem)
    {ld : Word → Option Word} (hld : ∀ a, ld a = Silmaril.X86.Ext.loadN mem a 8)
    {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H} {f : Silmaril.Wasm.Execution.Core.Frame}
    {W : Silmaril.Sim.X86.GM.Win} {σ : Silmaril.X86.State} (hS : StartAtMain s f mem W σ) :
    TabAt mem ghelloTab ∧
      Silmaril.Sim.WasiBridge.ElfWasiEquiv (blinkObs (ghelloC putsImpl) mem W ld ghelloFm ghelloTab s f)
        Silmaril.Sim.WasiBridge.G.helloWasi Silmaril.Sim.WasiBridge.S1 :=
  ghello_e2e hL hld putsImpl_meets (fun args k hp hk1 hk => putsImpl_admits (cstr_msg hL) args k hp hk1 hk) hS

end Silmaril.Sim.GlibcBridge
