module

public import Silmaril.Sim.GlibcBridge.Defs

/-!
# glibc hello relative to the `puts` contract

* `lrun_mono` (**assume-guarantee composition**): a linked run with implementations meeting
  the contracts is a linked run with the contracts.
* `enc_extStore`: the store after an import call encodes `extCore` (System V boundary).
* `ghello_lrun`: every linked run of `ghelloItems` with a `puts` meeting `putsC1` and `exitC`
  has observables `prefix of (msg.take k).map (wr 1) ++ [exit 0]`, `1 ≤ k ≤ 14`.
* `ghello_run_of`: conversely, if the `puts` admits each output `msg.take k`, each such trace
  is a linked run.
* `putsImpl_meets`, `putsImpl_admits`: `glibc.wat`'s `puts` meets `putsC1` and admits them.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Sim.X86.G
open Silmaril.Sim.WasiBridge
open Silmaril.Sim.WasiBridge.G

variable {H : Type} {s : Store H} {f : Frame}

/-! ## Composition -/

/-- **Assume-guarantee**: runs with implementations meeting the contracts are runs with the
contracts. -/
theorem lrun_mono {I C : Nat → ImportC} (hI : ∀ k, Meets (I k) (C k))
    {Ans : List Word → Word → Prop} {mem : Memory} {s : Store H} {p : List LItem}
    {evs : List LEv} {rest : List LItem} (h : LRun I Ans mem s f p evs rest) :
    LRun C Ans mem s f p evs rest := by
  induction h with
  | stop => exact .stop _ _ _
  | ins hc he _ ih => exact .ins hc he ih
  | sys ha hr hans _ ih => exact .sys ha hr hans ih
  | pending ha => exact .pending ha
  | ext ha hr hc _ ih => exact .ext ha hr (hI _ _ _ _ _ hc) ih
  | halt ha hc => exact .halt ha (hI _ _ _ _ _ hc)

theorem linkObs_mono {I C : Nat → ImportC} (hI : ∀ k, Meets (I k) (C k))
    {Ans : List Word → Word → Prop} {mem : Memory} {s : Store H} {p : List LItem} :
    Refines (linkObs I Ans mem s f p) (linkObs C Ans mem s f p) := by
  rintro o ⟨evs, rest, h, ho⟩
  exact ⟨evs, rest, lrun_mono hI h, ho⟩

/-! ## The call boundary -/

theorem regArgs_enc {σ : State} (hE : Enc s f σ) (regs : List Reg) :
    regArgs s f regs = some (regs.map σ.read) := by
  have h := hE.2.1
  induction regs with
  | nil => rfl
  | cons r rs ih =>
    simp only [regArgs, List.mapM_cons, h r, Val.i64] at ih ⊢
    simp [ih]

/-- Register writes, in order. -/
def writeRegs (σ : State) : List (Reg × Word) → State
  | [] => σ
  | (r, v) :: l => writeRegs (σ.write r v) l

theorem writeRegs_rip (σ : State) (l : List (Reg × Word)) : (writeRegs σ l).rip = σ.rip := by
  induction l generalizing σ with
  | nil => rfl
  | cons a l ih => exact (ih _).trans rfl

theorem writeRegs_flags (σ : State) (l : List (Reg × Word)) : (writeRegs σ l).flags = σ.flags := by
  induction l generalizing σ with
  | nil => rfl
  | cons a l ih => exact (ih _).trans rfl

theorem enc_updRegs {σ : State} (hE : Enc s f σ) (l : List (Reg × Word)) :
    Enc (updRegs s f l) f (writeRegs σ l) := by
  induction l generalizing s σ with
  | nil => exact hE
  | cons a l ih =>
    obtain ⟨r, v⟩ := a
    exact ih (enc_reg hE r v (σ.write r v) (regsAfter_write _ _ _ _ rfl) rfl rfl)

/-- The modelled flags, undefined. -/
def undefFlags (fl : Silmaril.X86.Flags) : Silmaril.X86.Flags :=
  { fl with carry := none, zero := none, sign := none, overflow := none }

/-- The core after an import call: `rax := v`, scratch registers `ws`, flags undefined,
`rip += len`. -/
def extCore (σ : State) (v : Word) (ws : Reg → Word) (len : Nat) : State :=
  { writeRegs (σ.write .rax v) (scratch.map fun q => (q, ws q)) with
    rip := σ.rip + BitVec.ofNat 64 len, flags := undefFlags σ.flags }

theorem enc_undef {σ : State} (hE : Enc s f σ) : Enc s f { σ with flags := undefFlags σ.flags } := by
  obtain ⟨hl, hr, hrip, ⟨b1, h1, -⟩, ⟨b2, h2, -⟩, ⟨b3, h3, -⟩, ⟨b4, h4, -⟩⟩ := hE
  exact ⟨hl, hr, hrip, ⟨b1, h1, trivial⟩, ⟨b2, h2, trivial⟩, ⟨b3, h3, trivial⟩, ⟨b4, h4, trivial⟩⟩

/-- **The import call is sound for the System V boundary.** -/
theorem enc_extStore {σ : State} (hE : Enc s f σ) (v : Word) (ws : Reg → Word) (len : Nat) :
    Enc (extStore s f σ.rip v ws len) f (extCore σ v ws len) := by
  have h₁ := enc_reg hE .rax v (σ.write .rax v) (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₂ := enc_undef (enc_updRegs h₁ (scratch.map fun q => (q, ws q)))
  refine Enc.next h₂ (extCore σ v ws len) rfl ?_ _ rfl
  show undefFlags σ.flags = undefFlags (writeRegs (σ.write .rax v) _).flags
  rw [writeRegs_flags]; rfl

/-! ## Inversion -/

variable {C : Nat → ImportC} {Ans : List Word → Word → Prop} {mem : Memory}

theorem lrun_ins_inv {i : Silmaril.X86.Ext.Instr} {n : Nat} {p : List LItem} {evs : List LEv}
    {rest : List LItem} (hw : LRun C Ans mem s f (.ins i n :: p) evs rest) {σ σ' : State}
    (hE : Enc s f σ) {m : Memory} (hx : Silmaril.X86.Ext.exec i σ m n = .ok σ' m) :
    (evs = [] ∧ rest = .ins i n :: p) ∨ ∃ s' : Store H, Enc s' f σ' ∧ LRun C Ans mem s' f p evs rest := by
  cases hw with
  | stop => exact .inl ⟨rfl, rfl⟩
  | ins hc he hw' =>
    obtain ⟨-, s'', he', hE', -⟩ := emit_sound hc hE hx
    rw [he] at he'
    cases he'
    exact .inr ⟨_, hE', hw'⟩

theorem lrun_ext_inv {k : Nat} {regs : List Reg} {len : Nat} {p : List LItem} {evs : List LEv}
    {rest : List LItem} (hw : LRun C Ans mem s f (.ext k regs len :: p) evs rest) {σ : State}
    (hE : Enc s f σ) :
    (evs = [] ∧ rest = .ext k regs len :: p) ∨
    (∃ o, C k mem (regs.map σ.read) o none ∧ evs = [.ext k (regs.map σ.read) o none]) ∨
    ∃ o v ws evs', C k mem (regs.map σ.read) o (some v) ∧
      evs = .ext k (regs.map σ.read) o (some v) :: evs' ∧
      LRun C Ans mem (extStore s f σ.rip v ws len) f p evs' rest := by
  have ha := regArgs_enc hE regs
  have hr := hE.2.2.1
  cases hw with
  | stop => exact .inl ⟨rfl, rfl⟩
  | halt h hc => rw [ha] at h; cases h; exact .inr (.inl ⟨_, hc, rfl⟩)
  | ext h hrip hc hw' =>
    rw [ha] at h; cases h
    rw [hr] at hrip
    simp only [Option.some.injEq, val_i64_inj] at hrip
    subst hrip
    exact .inr (.inr ⟨_, _, _, _, hc, rfl, hw'⟩)

/-! ## Bytes and characters -/

theorem toChars_left (b : Byte) : BitVec.ofNat 8 (Char.ofNat b.toNat).toNat = b := by
  revert b; decide

theorem toChars_inj {a b : List Byte} (h : toChars a = toChars b) : a = b := by
  have := congrArg (List.map fun c : Char => BitVec.ofNat 8 c.toNat) h
  simpa [toChars, List.map_map, Function.comp_def, toChars_left] using this

theorem toChars_append (a b : List Byte) : toChars (a ++ b) = toChars a ++ toChars b :=
  List.map_append

theorem toChars_take (a : List Byte) (n : Nat) : toChars (a.take n) = (toChars a).take n :=
  List.map_take ..

theorem toChars_length (a : List Byte) : (toChars a).length = a.length := List.length_map ..

theorem toChars_nl : toChars [10] = ['\n'] := by decide

/-- The outputs `putsGlibc` allows for `s` are the prefixes of `s ++ "\n"`. -/
theorem putsGlibc_prefix {s w : List Byte} {r : Int}
    (h : Silmaril.Libc.putsGlibc (toChars s) (toChars w) r) : w <+: s ++ [10] := by
  have hp : toChars w <+: toChars (s ++ [10]) := by
    rw [toChars_append, toChars_nl]
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · exact h
  rw [List.prefix_iff_eq_take] at hp ⊢
  rw [toChars_length, ← toChars_take] at hp
  exact toChars_inj hp

/-! ## The glibc hello -/

theorem msgS_nl : msgS ++ [10] = helloMsg := by decide

theorem exec_xor32 (σ : State) (m : Memory) :
    ∃ σ', Silmaril.X86.Ext.exec (.alu .d .xor (.reg .rax) .rax) σ m 2 = .ok σ' m ∧
      σ'.read .rax = 0 := by
  refine ⟨_, rfl, ?_⟩
  simp only [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.AluOp.resultN]
  apply BitVec.eq_of_toNat_eq
  simp
  erw [BitVec.toNat_xor, Nat.xor_self]

theorem levsObs_cons (e : LEv) (evs : List LEv) :
    levsObs mem (e :: evs) = e.obs mem ++ levsObs mem evs := List.flatMap_cons ..

/-- **Every linked run of the glibc hello**, with a `puts` meeting `putsC1`, has the
observables of the WASI hello for some `1 ≤ k ≤ 14`. -/
theorem ghello_lrun {P : ImportC} (hP : Meets P putsC1) (hstr : cstr mem msgAddr = some msgS)
    {σ : State} (hE : Enc s f σ) {evs : List LEv} {rest : List LItem}
    (hw : LRun (ghelloC P) Ans mem s f ghelloItems evs rest) :
    ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ levsObs mem evs <+: helloObs k := by
  have nil : levsObs mem [] <+: helloObs 1 := List.nil_prefix
  simp only [ghelloItems] at hw
  rcases lrun_ins_inv hw hE (exec_movabs .rdi msgAddr σ mem 10) with ⟨rfl, -⟩ | ⟨s₁, hE₁, hw⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  rcases lrun_ext_inv hw hE₁ with ⟨rfl, -⟩ | ⟨o, hc, -⟩ | ⟨o, v, ws, evs', hc, rfl, hw₁⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  · obtain ⟨⟨_, _, _, _, _, -, -, -, -, h, -⟩, -⟩ := hP _ _ _ _ hc
    cases h
  obtain ⟨⟨p, s', w, r, v', hp, hs, hpg, rfl, -, -⟩, hne⟩ := hP _ _ _ _ hc
  obtain rfl : msgAddr = p := by
    simpa only [sysvArgs, List.map_cons, movStep_read, ite_true, List.head?_cons,
      Option.some.injEq] using hp
  obtain rfl : msgS = s' := Option.some.inj (hstr.symm.trans hs)
  have hpre : w <+: helloMsg := by rw [← msgS_nl]; exact putsGlibc_prefix hpg
  have hw0 : w ≠ [] := by rintro rfl; exact hne rfl
  have hk1 : 1 ≤ w.length := List.length_pos_iff.2 hw0
  have hk : w.length ≤ 14 := by have := hpre.length_le; simpa [helloMsg] using this
  have hwt : w = helloMsg.take w.length := List.prefix_iff_eq_take.1 hpre
  have hobs : ∀ (a : List Word) (tail : List LEv),
      levsObs mem (.ext 0 a (w.map (.wr 1)) (some v) :: tail) = w.map (.wr 1) ++ levsObs mem tail :=
    fun _ _ => rfl
  have hE₂ : Enc (extStore s₁ f _ v ws 5) f (extCore (movStep σ .rdi msgAddr 10) v ws 5) :=
    enc_extStore hE₁ v ws 5
  obtain ⟨σ₃, hx, h0⟩ := exec_xor32 (extCore (movStep σ .rdi msgAddr 10) v ws 5) mem
  rcases lrun_ins_inv hw₁ hE₂ hx with ⟨rfl, -⟩ | ⟨s₃, hE₃, hw₃⟩
  · refine ⟨w.length, hk1, hk, ?_⟩
    rw [hobs, levsObs, List.flatMap_nil, List.append_nil, helloObs, ← hwt]
    exact List.prefix_append _ _
  rcases lrun_ext_inv hw₃ hE₃ with ⟨rfl, -⟩ | ⟨o, hc, rfl⟩ | ⟨o, v, ws, evs', hc, rfl, -⟩
  · refine ⟨w.length, hk1, hk, ?_⟩
    rw [hobs, levsObs, List.flatMap_nil, List.append_nil, helloObs, ← hwt]
    exact List.prefix_append _ _
  · obtain ⟨a, ha, rfl, -⟩ : exitC mem _ _ none := hc
    have ha0 : a = 0 := by
      simpa only [List.map_cons, List.map_nil, h0, List.head?_cons, Option.some.injEq] using ha.symm
    refine ⟨w.length, hk1, hk, ?_⟩
    rw [hobs, helloObs, ← hwt]
    simp [levsObs, LEv.obs, ha0]
  · obtain ⟨_, -, -, h⟩ := hc
    cases h

/-- **The converse**: if the `puts` admits every output `msg.take k` (`1 ≤ k ≤ 14`), each
WASI hello trace is the observable trace of a linked run. -/
theorem ghello_run_of {P : ImportC}
    (hA : ∀ args k, args.head? = some msgAddr → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    {σ : State} (hE : Enc s f σ) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 14) :
    ∃ evs rest, LRun (ghelloC P) Ans mem s f ghelloItems evs rest ∧
      levsObs mem evs = helloObs k := by
  have hc1 : emit (.movabs .rdi msgAddr) 10 = some _ := rfl
  obtain ⟨-, s₁, he₁, hE₁, -⟩ := emit_sound hc1 hE (exec_movabs .rdi msgAddr σ mem 10)
  obtain ⟨v, hv⟩ := hA (sysvArgs.map (movStep σ .rdi msgAddr 10).read) k (by simp [sysvArgs]) hk1 hk
  have hE₂ := enc_extStore hE₁ v (fun _ => 0) 5
  obtain ⟨σ₃, hx, h0⟩ := exec_xor32 (extCore (movStep σ .rdi msgAddr 10) v (fun _ => 0) 5) mem
  have hc3 : emit (.alu .d .xor (.reg .rax) .rax) 2 = some _ := rfl
  obtain ⟨-, s₃, he₃, hE₃, -⟩ := emit_sound hc3 hE₂ hx
  have hexit : exitC mem ([Reg.rax].map σ₃.read) [.exit 0] none :=
    ⟨0, by simp [h0], by decide, rfl⟩
  refine ⟨_, _, .ins hc1 he₁ (.ext (regArgs_enc hE₁ _) hE₁.2.2.1 hv
    (.ins hc3 he₃ (.halt (regArgs_enc hE₃ _) hexit))), ?_⟩
  simp [levsObs, LEv.obs, helloObs]

/-! ## `glibc.wat`'s `puts` -/

theorem cstrAux_length (rd : Word → Option Byte) : ∀ (n : Nat) (p : Word) {s : List Byte},
    cstrAux rd p n = some s → s.length ≤ n
  | 0, _, _, h => by simp [cstrAux] at h
  | n + 1, p, s, h => by
    simp only [cstrAux] at h
    split at h
    · cases h
    · split at h
      · cases h; simp
      · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
        have := cstrAux_length rd n (p + 1) ht
        simp; omega

/-- **`glibc.wat`'s `puts` meets the contract.** -/
theorem putsImpl_meets : Meets putsImpl putsC1 := by
  rintro mem args o ret ⟨p, s, k, v, hp, hs, hk1, hk, rfl, rfl, hv⟩
  have hlen : s.length ≤ 65536 := cstrAux_length _ _ _ hs
  have hne : (s ++ [10]).take k ≠ [] := by
    simp only [ne_eq, List.take_eq_nil_iff, not_or]; refine ⟨by omega, by simp⟩
  refine ⟨⟨p, s, (s ++ [10]).take k, _, v, hp, hs, ?_, rfl, rfl, hv⟩, by simpa using hne⟩
  by_cases hfull : k = s.length + 1
  · subst hfull
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    refine .inl ⟨?_, ?_⟩
    · rw [List.take_of_length_le (by simp), toChars_append, toChars_nl]
    · rw [toChars_length]; omega
  · simp only [hfull, ↓reduceIte]
    refine .inr ⟨?_, rfl⟩
    rw [← toChars_nl, ← toChars_append]
    exact (List.take_prefix _ _).map _

/-- `glibc.wat`'s `puts` admits every output of the hello. -/
theorem putsImpl_admits {p : Word} (hstr : cstr mem p = some msgS) (args : List Word) (k : Nat)
    (hp : args.head? = some p) (hk1 : 1 ≤ k) (hk : k ≤ 14) :
    ∃ v, putsImpl mem args ((helloMsg.take k).map (.wr 1)) (some v) := by
  have hl : msgS.length = 13 := by decide
  by_cases h : k = 14
  · subst h
    exact ⟨_, p, msgS, 14, BitVec.ofInt 64 14, hp, hstr, by omega, by omega, by rw [msgS_nl],
      rfl, by rw [hl]; unfold RetInt; decide⟩
  · exact ⟨_, p, msgS, k, BitVec.ofInt 64 (-1), hp, hstr, hk1, by omega, by rw [msgS_nl], rfl,
      by rw [hl]; simp only [show k ≠ 13 + 1 by omega, ↓reduceIte]; unfold RetInt; decide⟩


/-! ## glibc hello ≡ WASI hello, relative to the `puts` contract -/

/-- **Composition, ⊑**: for every `puts` implementation meeting `putsC1`, the linked glibc
hello only has observable traces of the WASI hello. -/
theorem ghello_refines {P : ImportC} (hP : Meets P putsC1) (hstr : cstr mem msgAddr = some msgS)
    {σ : State} (hE : Enc s f σ) :
    Refines (linkObs (ghelloC P) Ans mem s f ghelloItems) (helloWasi.obs S1) := by
  rintro o ⟨evs, rest, hw, ho⟩
  obtain ⟨k, hk1, hk, hp⟩ := ghello_lrun hP hstr hE hw
  exact (helloWasi_obs o).2 ⟨k, hk1, hk, ho.trans hp⟩

/-- **Composition, ≡**: for every `puts` implementation meeting `putsC1` and admitting each
output of the hello, the linked glibc hello ≡ the WASI hello. -/
theorem ghello_equiv {P : ImportC} (hP : Meets P putsC1)
    (hA : ∀ args k, args.head? = some msgAddr → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    (hstr : cstr mem msgAddr = some msgS) {σ : State} (hE : Enc s f σ) :
    ElfWasiEquiv (linkObs (ghelloC P) Ans mem s f ghelloItems) helloWasi S1 := by
  refine ⟨ghello_refines hP hstr hE, fun o ho => ?_⟩
  obtain ⟨k, hk1, hk, hp⟩ := (helloWasi_obs o).1 ho
  obtain ⟨evs, rest, hw, he⟩ := ghello_run_of hA hE hk1 hk
  exact ⟨evs, rest, hw, he ▸ hp⟩

/-- **`glibc.wat`'s `puts` linked in**: the glibc hello ≡ the WASI hello. -/
theorem ghello_equiv_impl (hstr : cstr mem msgAddr = some msgS) {σ : State} (hE : Enc s f σ) :
    ElfWasiEquiv (linkObs (ghelloC putsImpl) Ans mem s f ghelloItems) helloWasi S1 :=
  ghello_equiv putsImpl_meets (putsImpl_admits hstr) hstr hE

/-- **Relative to the contract itself** (assume-guarantee: program ⊗ `putsC1` ≡ WASI hello). -/
theorem ghello_equiv_contract (hstr : cstr mem msgAddr = some msgS) {σ : State}
    (hE : Enc s f σ) :
    ElfWasiEquiv (linkObs (ghelloC putsC1) Ans mem s f ghelloItems) helloWasi S1 :=
  ghello_equiv (fun _ _ _ _ h => h)
    (fun args k hp hk1 hk => by
      obtain ⟨v, hv⟩ := putsImpl_admits hstr args k hp hk1 hk
      exact ⟨v, putsImpl_meets _ _ _ _ hv⟩) hstr hE

/-- **glibc-linked hello ≡ static hello process**: the linked glibc hello (any `puts` meeting
`putsC1` and admitting the outputs) has the observable traces of the static `hello` process
under LPS's Linux model (`hello_equiv_lps`). -/
theorem ghello_equiv_static {P : ImportC} (hP : Meets P putsC1)
    (hA : ∀ args k, args.head? = some msgAddr → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    (hstr : cstr mem msgAddr = some msgS) {σ : State} (hE : Enc s f σ)
    (segs : List Silmaril.Process.LPS.Segment) {mem₀ : Memory} {σ₀ : State}
    (hb : BytesAt mem₀ σ₀.rip helloBytes) (hmsg : wsrc mem₀ msgAddr 14#64 = helloMsg)
    (hσ : FlagsDef σ₀) (e : Silmaril.Process.LPS.Model) (hok : LpsOk e) (hchan : LpsChan e 1) :
    Equiv (linkObs (ghelloC P) Ans mem s f ghelloItems)
      (procObs lpsStep (lpsEnv segs) ⟨σ₀, mem₀⟩ e) := by
  have h₁ := ghello_equiv (Ans := Ans) hP hA hstr hE
  have h₂ := (hello_equiv_lps segs hb hmsg hσ e hok hchan).2
  exact ⟨fun o ho => h₂.2 o (h₁.1 o ho), fun o ho => h₁.2 o (h₂.1 o ho)⟩

end Silmaril.Sim.GlibcBridge
