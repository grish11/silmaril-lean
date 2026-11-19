module

public import Silmaril.Sim.GlibcBridge.Link.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.RelIsa.Thms

/-! # Dynamic linking: generic theorems (DL1)

PROVED (standard axioms):

* `resolveIn_skip`, `resolveIn_head`: lookup passes objects that do not define the name and
  stops at the first that does. `resolveIn_noInterpose`: if the executable does not define
  `n` and the library right after it does, `n` resolves to the library's own definition, whatever
  follows. This is the one place where interposition enters: `Sat` is stated on the resolved
  map, so a `Sat` hypothesis on the resolved map needs no such lemma.
* `got_word`: under `EagerLoaded`, a `GLOB_DAT`/`JUMP_SLOT` slot holds the resolved address, and
  resolution succeeds for a non-weak reference.
* `jmpRip_exec`: `jmp *d(%rip)` (`FF 25 d32`) jumps to the word at `next + d`.
* `must_of_step`: on an `ExtendsOpen9` machine, a retiring `Open9` step carries `Must` back;
  `extendsOpen9_ofFun`: `ofFun Open9.step` is such a machine; `retAddr_congr`.
* `Must`-level spec order: `Contract.Le.refl/trans`, `meets_mono`, `LibSpec.Le.refl/trans`,
  `LibSpec.le_append`, `sat_mono`, `exports_mono`, and the link step `exports_sat`: a library's
  export spec is a spec of the resolved map, under `EagerLoaded`, when no earlier object
  interposes.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge.Link

open Silmaril.X86 (Word Byte MState State)
open Silmaril.Process (Memory)
open Silmaril.X86 (RelIsa)

/-! ## Lookup -/

theorem resolveIn_skip {ifn : Word → Option Word} {o : Obj} {b : Word} {rest : LinkMap} {n : Name}
    (h : o.defines n = none) : resolveIn ifn ((o, b) :: rest) n = resolveIn ifn rest n := by
  simp [resolveIn, h]

theorem resolveIn_head {ifn : Word → Option Word} {o : Obj} {b : Word} {rest : LinkMap} {n : Name}
    (h : o.defines n ≠ none) : resolveIn ifn ((o, b) :: rest) n = resolveIn ifn [(o, b)] n := by
  cases e : o.defines n with
  | none => exact absurd e h
  | some d => simp [resolveIn, e]

/-- **No interposition**: the executable does not define `n`, the next object does. -/
theorem resolveIn_noInterpose {ifn : Word → Option Word} {exe L : Obj} {b lb : Word}
    {rest : LinkMap} {n : Name} (he : exe.defines n = none) (hL : L.defines n ≠ none) :
    resolveIn ifn ((exe, b) :: (L, lb) :: rest) n = resolveIn ifn [(L, lb)] n := by
  rw [resolveIn_skip he, resolveIn_head hL]

theorem resolveIn_single_ne {ifn : Word → Option Word} {L : Obj} {lb : Word} {n : Name}
    {f : Word} (h : resolveIn ifn [(L, lb)] n = some f) : L.defines n ≠ none := by
  intro e; simp [resolveIn, e] at h

/-! ## The GOT -/

/-- **A symbol slot holds the resolved address.** -/
theorem got_word {lm : LinkMap} {ifn : Word → Option Word} {mem : Memory} (hL : EagerLoaded lm ifn mem)
    {e : Obj × Word} (he : e ∈ lm) {r : Rel} (hr : r ∈ e.1.rels) (hk : r.kind = 6 ∨ r.kind = 7)
    (hw : r.weak = false) :
    ∃ f, resolveIn ifn lm r.sym = some f ∧
      Silmaril.X86.Ext.loadN mem (e.2 + BitVec.ofNat 64 r.offset) 8 = some f := by
  obtain ⟨v, hv, hload⟩ := (hL.image e he).relocated r hr
  have h8 : r.kind ≠ 8 := by omega
  simp only [relValue, h8, ite_false, hk, ite_true] at hv
  cases e' : resolveIn ifn lm r.sym with
  | none => simp [e', hw] at hv
  | some f =>
    simp [e'] at hv
    exact ⟨f, rfl, hv ▸ hload⟩

/-! ## The PLT jump -/

/-- `jmp *d(%rip)` jumps to the word at `next + d`. -/
theorem jmpRip_exec (d : BitVec 32) (s : State) (mem : Memory) (next v : Word)
    (h : Silmaril.X86.Ext.loadN mem (next + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.execNew (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d))) s mem next =
      .ok { s with rip := v } mem := by
  simp [Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.Mem.addr,
    Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value, h, Silmaril.X86.Ext.Sz.bytes]

/-! ## Machines -/

/-- One retiring `Open9` step carries `Must` back on an `ExtendsOpen9` machine. -/
theorem must_of_step {A : RelIsa MState} (hA : ExtendsOpen9 A) {Q : MState → Prop} {m m' : MState}
    (hs : Silmaril.X86.Open9.step m = some m')
    (h : RelIsa.Must A (fun _ => True) Q m') : RelIsa.Must A (fun _ => True) Q m := by
  refine RelIsa.Must.step trivial ?_ ?_
  · intro hstop; cases (hA m m' hs .stop).1 hstop
  · intro t ht
    have := (hA m m' hs (.ok t)).1 ht
    cases this; exact h

/-- `ofFun Open9.step` extends `Open9` (so `ExtendsOpen9` is not vacuous). -/
theorem extendsOpen9_ofFun : ExtendsOpen9 (RelIsa.ofFun Silmaril.X86.Open9.step) := by
  intro m m' h r
  simp [RelIsa.ofFun, h]

/-- The return address depends only on the memory and `rsp`. -/
theorem retAddr_congr {m m' : MState} (hm : m.memory = m'.memory)
    (hr : m.core.read .rsp = m'.core.read .rsp) : retAddr m = retAddr m' := by
  simp only [retAddr, Silmaril.X86.popWord, hm, hr]
  cases m'.memory.readBytes (m'.core.read .rsp).toNat 8 with
  | none => rfl
  | some bs => cases h : Silmaril.X86.wordOfBytes? bs <;> simp [h]

/-! ## The spec order -/

theorem Contract.Le.refl (c : Contract) : c.Le c := ⟨fun _ h => h, fun _ _ _ h => h⟩

theorem Contract.Le.trans {c d e : Contract} (h₁ : c.Le d) (h₂ : d.Le e) : c.Le e :=
  ⟨fun m h => h₂.1 m (h₁.1 m h), fun m m' hc he => h₁.2 m m' hc (h₂.2 m m' (h₁.1 m hc) he)⟩

/-- Code meeting a stronger contract meets the weaker one. -/
theorem meets_mono {A : RelIsa MState} {P P' : Memory → Prop} {f : Word} {c d : Contract}
    (hP : ∀ mem, P' mem → P mem) (hle : c.Le d) (h : Meets A P f d) : Meets A P' f c :=
  fun m hm hrip hpre =>
    RelIsa.Must.mono (fun _ h => h) (fun m' hq => hle.2 m m' hpre hq)
      (h m (hP _ hm) hrip (hle.1 m hpre))

theorem LibSpec.Le.refl (S : LibSpec) : S.Le S := fun p hp => ⟨p, hp, rfl, Contract.Le.refl _⟩

theorem LibSpec.Le.trans {S T U : LibSpec} (h₁ : S.Le T) (h₂ : T.Le U) : S.Le U := by
  intro p hp
  obtain ⟨q, hq, hn, hc⟩ := h₁ p hp
  obtain ⟨r, hr, hn', hc'⟩ := h₂ q hq
  exact ⟨r, hr, hn'.trans hn, hc.trans hc'⟩

/-- Adding entries strengthens a spec. -/
theorem LibSpec.le_append (S T : LibSpec) : S.Le (S ++ T) :=
  fun p hp => ⟨p, List.mem_append_left _ hp, rfl, Contract.Le.refl _⟩

/-- **A stronger spec implies a weaker one**, on any address map. -/
theorem sat_mono {A : RelIsa MState} {P P' : Memory → Prop} {addr : Name → Option Word}
    {S T : LibSpec} (hP : ∀ mem, P' mem → P mem) (hle : S.Le T) (h : Sat A P addr T) :
    Sat A P' addr S := by
  intro p hp
  obtain ⟨q, hq, hn, hc⟩ := hle p hp
  obtain ⟨f, hf, hm⟩ := h q hq
  exact ⟨f, hn ▸ hf, meets_mono hP hc hm⟩

/-- Export specs are monotone too. -/
theorem exports_mono {A : RelIsa MState} {L : Obj} {lb : Word} {ifn : Word → Option Word}
    {S T : LibSpec} (hle : S.Le T) (h : Exports A L lb ifn T) : Exports A L lb ifn S :=
  fun lm hm => sat_mono (fun _ h => h) hle (h lm hm)

/-- **Link step**: a library's export spec is a spec of the resolved map when the executable
defines none of its names and the library comes right after it in the search order. -/
theorem exports_sat {A : RelIsa MState} {ifn : Word → Option Word} {exe L : Obj} {b lb : Word}
    {rest : LinkMap} {S : LibSpec} (hexe : ∀ p ∈ S, exe.defines p.1 = none)
    (hL : Exports A L lb ifn S) :
    Sat A (EagerLoaded ((exe, b) :: (L, lb) :: rest) ifn)
      (resolveIn ifn ((exe, b) :: (L, lb) :: rest)) S := by
  have hmem : (L, lb) ∈ (exe, b) :: (L, lb) :: rest := by simp
  intro p hp
  obtain ⟨f, hf, hm⟩ := hL _ hmem p hp
  refine ⟨f, ?_, meets_mono (fun mem h => h.image _ hmem) (Contract.Le.refl _) hm⟩
  rw [resolveIn_noInterpose (hexe p hp) (resolveIn_single_ne hf)]
  exact hf

end Silmaril.Sim.GlibcBridge.Link
