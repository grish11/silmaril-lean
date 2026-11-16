module

public import Silmaril.Proofs.Sim.X86.GM.Progress
public import Silmaril.Sim.X86.Loop.Thms
public import Silmaril.Machine.X86.Open9.Thms

/-!
# GM: programs with memory — reduction, termination, machine runs

* `xrun_twpM`: a window-respecting x86 run is matched by every run of the dispatcher (`TWP`),
  ending in a store encoding the final state and window;
* **`xlproblemM_of_lproblemM`**: `LProblemM` (Wasm) solves `XLProblemM` (x86);
* **`xrun_existsM`**: a measured Wasm invariant of the dispatcher and x86 progress give a
  window-respecting run (termination; the window side condition comes from the Wasm side,
  `emitM_holds`);
* **`reaches_of_xrunM`**: such a run, of code placed in memory outside the window (`TabAtM`), is
  a run of the open machine `Silmaril.Machine.X86.Open.step` (every `ret` an ordinary step).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Core (exec Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP TWP TSafe)

variable {H : Type}

theorem lookup_compileM {W : Win} {tab : XTab} (hs : SupportedM W tab) {w : Word} :
    match lookupI tab w with
    | some (i, n) => ∃ code, lookupC (compileTabM W tab) w = some code ∧ emitM W i n = some code
    | none => lookupC (compileTabM W tab) w = none := by
  induction tab with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨a, i, n⟩ := e
    have ht : SupportedM W t := fun e he => hs e (List.mem_cons_of_mem _ he)
    by_cases hwa : w = a
    · obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp (hs (a, i, n) (by simp))
      simp only [lookupI, hwa, ite_true, compileTabM, List.map_cons, lookupC]
      exact ⟨code, by simp [hcode], hcode⟩
    · simp only [lookupI, hwa, ite_false, compileTabM, List.map_cons, lookupC]
      exact ih ht

/-- **A window-respecting x86 run is matched by the dispatcher** (every run, terminating). -/
theorem xrun_twpM {P : Profile} {host : HostSemantics H} {W : Win} {tab : XTab}
    (hs : SupportedM W tab) {k : Nat} {σ σ' : State} {mem mem' : Silmaril.Process.Memory}
    (hx : XRunM tab W k σ mem σ' mem') {s : Store H} {f : Frame} (hE : Enc s f σ)
    (hM : MemEnc s f mem W) :
    TWP P host s f (expression (dispCode (compileTabM W tab)))
      (fun s' f' o => o = .normal [] ∧ f' = f ∧ Enc s' f σ' ∧ MemEnc s' f mem' W) := by
  refine dispatch_twp (compileTabM W tab)
    (fun k s => ∃ σ mem, Enc s f σ ∧ MemEnc s f mem W ∧ XRunM tab W k σ mem σ' mem') _ ?_
    ⟨σ, mem, hE, hM, hx⟩
  rintro k s ⟨σ, mem, hE, hM, hx⟩
  refine ⟨σ.rip, hE.2.2.1, ?_⟩
  have hl := lookup_compileM hs (w := σ.rip)
  cases hx with
  | done hn =>
    rw [hn] at hl
    rw [hl]
    exact ⟨rfl, rfl, hE, hM⟩
  | step hi he hw _ hr =>
    rw [hi] at hl
    obtain ⟨code, hc, hcode⟩ := hl
    rw [hc]
    obtain ⟨s', hex, hE', hM', -⟩ := emitM_sound hcode hE hM he hw
    exact ⟨s', hex, _, Nat.lt_succ_self _, _, _, hE', hM', hr⟩

/-! ## A store encoding a state and a window -/

/-- A memory type for the canonical store. -/
def memType : MemoryType := ⟨.i32, ⟨0, none⟩⟩

/-- The canonical store encoding `σ` and the window of `mem`. -/
noncomputable def encStoreM (σ : State) (mem : Silmaril.Process.Memory) (W : Win) : Store H :=
  { (encStore (H := H) σ) with mems := [⟨memType, winBytes mem W⟩] }

/-- Its frame: globals `0..22`, memory `0`. -/
def encFrameM : Frame := { module := { globals := List.range 23, mems := [0] } }

theorem winBytes_size (mem : Silmaril.Process.Memory) (W : Win) : (winBytes mem W).size = W.size := by
  simp [winBytes, ByteArray.size]

theorem wbytes_encStoreM (σ : State) (mem : Silmaril.Process.Memory) (W : Win) :
    wbytes (encStoreM (H := H) σ mem W) encFrameM = some (winBytes mem W) := by
  rfl

theorem enc_encStoreM (σ : State) (mem : Silmaril.Process.Memory) (W : Win) :
    Enc (encStoreM (H := H) σ mem W) encFrameM σ := by
  have h := enc_encStore (H := H) σ
  have hg : ∀ l, gval (encStoreM (H := H) σ mem W) encFrameM l = gval (encStore (H := H) σ) encFrame l :=
    fun l => by rw [gval_eq, gval_eq]; rfl
  obtain ⟨⟨ha, hi⟩, hr, hri, h1, h2, h3, h4⟩ := h
  refine ⟨⟨fun l => ha l, fun l₁ l₂ a => hi l₁ l₂ a⟩, ?_⟩
  simp only [hg]
  exact ⟨hr, hri, h1, h2, h3, h4⟩

theorem memEnc_encStoreM {σ : State} {mem : Silmaril.Process.Memory} {W : Win} (hW : WinOK mem W) :
    MemEnc (encStoreM (H := H) σ mem W) encFrameM mem W := by
  obtain ⟨h32, hlim, hb⟩ := hW
  refine ⟨_, wbytes_encStoreM σ mem W, by rw [winBytes_size], h32, hlim, fun k hk => ?_⟩
  obtain ⟨hr, hw, hs⟩ := hb k hk
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨hr, hw, x, hx, ?_⟩
  simp only [winBytes, List.getElem?_map, List.getElem?_range hk, Option.map_some, hx,
    Option.getD_some]

/-- **The reduction with memory.** -/
theorem xlproblemM_of_lproblemM {P : Profile} {host : HostSemantics H} {W : Win} {tab : XTab}
    (hs : SupportedM W tab) {Pre : (Reg → Word) → Word → ByteArray → Prop}
    {Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → Prop}
    (hW : LProblemM (H := H) P host W (dispCode (compileTabM W tab)) Pre Post) :
    XLProblemM tab W Pre Post := by
  intro σ σ' mem mem' k hwin hpre hx
  have hE := enc_encStoreM (H := H) σ mem W
  have hM := memEnc_encStoreM (H := H) (σ := σ) hwin
  obtain ⟨⟨s', f', c'⟩, hsteps, o, hexit, rfl, rfl, hE', -⟩ :=
    tsafe_run (xrun_twpM (P := P) (host := host) hs hx hE hM)
  have hc : c' = vals [] := hexit
  subst hc
  have hH := hW _ _ σ.read σ.rip _ hE.gregs hE.2.2.1 (wbytes_encStoreM σ mem W)
    (by rw [winBytes_size]) hpre
  obtain ⟨-, hpost⟩ := HWP.sound_vals hH hsteps
  exact hpost σ'.read σ'.rip hE'.2.1 hE'.2.2.1

/-- **x86 runs with memory exist** (termination) from a measured Wasm invariant. -/
theorem xrun_existsM {W : Win} {tab : XTab} (hs : SupportedM W tab) {f : Frame}
    (J : Nat → Store H → Prop)
    (hstep : ∀ k s, J k s → ∀ w code, gval s f .rip = some (Val.i64 w) →
      lookupC (compileTabM W tab) w = some code →
      ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, J k' s')
    (D : State → Prop)
    (hprog : ∀ σ mem i n, D σ → lookupI tab σ.rip = some (i, n) → (∃ s : Store H, MemEnc s f mem W) →
      (∀ a k, access i σ n = some (a, k) → W.HoldsK k a) → (emitM W i n).isSome →
      ∃ σ₁ mem₁, Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ mem₁ ∧ D σ₁) :
    ∀ k (s : Store H) σ mem, J k s → Enc s f σ → MemEnc s f mem W → D σ →
      ∃ n σ' mem', XRunM tab W n σ mem σ' mem' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s σ mem hJ hE hM hD
  have hl := lookup_compileM hs (w := σ.rip)
  cases hi : lookupI tab σ.rip with
  | none => exact ⟨0, σ, mem, .done hi⟩
  | some e =>
    obtain ⟨i, n⟩ := e
    rw [hi] at hl
    obtain ⟨code, hc, hcode⟩ := hl
    obtain ⟨s', he, k', hk', hJ'⟩ := hstep k s hJ σ.rip code hE.2.2.1 hc
    have hw := emitM_holds hcode hE hM he
    obtain ⟨σ₁, mem₁, hx, hD₁⟩ := hprog σ mem i n hD hi ⟨s, hM⟩ hw (by rw [hcode]; rfl)
    obtain ⟨s₁, he₁, hE₁, hM₁, hww⟩ := emitM_sound hcode hE hM hx hw
    rw [he] at he₁
    obtain rfl : s' = s₁ := by simp only [Option.some.injEq, Prod.mk.injEq] at he₁; exact he₁.1
    obtain ⟨n', σ', mem', hr⟩ := ih k' hk' s' σ₁ mem₁ hJ' hE₁ hM₁ hD₁
    exact ⟨n' + 1, σ', mem', .step hi hx hw hww hr⟩

/-! ## Runs of the open machine -/

/-- The code of the table is in memory, each instruction's bytes executable and outside the
window. -/
def TabAtM (mem : Silmaril.Process.Memory) (W : Win) (tab : XTab) : Prop :=
  ∀ e ∈ tab, ∃ bytes, mem.fetchBytes e.1.toNat e.2.2 = some bytes ∧
    Silmaril.X86.Ext.decode bytes = some e.2 ∧ ∀ o < e.2.2, ¬ W.Mem (e.1.toNat + o)

theorem TabAtM.preserve {mem mem' : Silmaril.Process.Memory} {W : Win} {tab : XTab}
    (h : TabAtM mem W tab) (hw : mem.WritesWithin mem' W.Mem) : TabAtM mem' W tab := by
  intro e he
  obtain ⟨bytes, hf, hd, ho⟩ := h e he
  exact ⟨bytes, by rw [hw.fetchBytes ho]; exact hf, hd, ho⟩

/-- **A window-respecting run of code in memory is a run of the open machine.** -/
theorem run_of_xrunM {W : Win} {tab : XTab} (hs : SupportedM W tab) :
    ∀ {k σ mem σ' mem'}, XRunM tab W k σ mem σ' mem' → TabAtM mem W tab →
      Silmaril.Machine.Execution.run Silmaril.Machine.X86.Open.step k ⟨σ, mem⟩ =
        some ⟨σ', mem'⟩ ∧ mem.WritesWithin mem' W.Mem
  | _, _, _, _, _, .done _, _ => ⟨rfl, Silmaril.Process.Memory.WritesWithin.refl _ _⟩
  | _, σ, mem, _, _, .step (i := i) (n := n) (σ₁ := σ₁) (mem₁ := mem₁) hi hx _ hww hr, hcode => by
    have hm := lookupI_mem hi
    obtain ⟨bytes, hfb, hdec, -⟩ := hcode _ hm
    have hf : Silmaril.X86.Ext.fetch mem σ.rip.toNat = .decoded i n :=
      Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bytes, hfb, hdec⟩
    have hlen := Silmaril.X86.Ext.fetch_length hf
    have hstep : Silmaril.Machine.X86.Open.step ⟨σ, mem⟩ = some ⟨σ₁, mem₁⟩ := by
      simp only [Silmaril.Machine.X86.Open.step]
      rw [Silmaril.X86.Ext8.fetch_of_ne_undecodable (by rw [hf]; simp), hf]
      simp only [Silmaril.Machine.X86.Open.ofResult]
      rw [← hlen, hx]
    obtain ⟨hrun, hw'⟩ := run_of_xrunM hs hr (hcode.preserve hww)
    refine ⟨?_, hww.trans hw'⟩
    rw [Silmaril.Machine.Execution.run_succ, hstep, Option.bind_some]
    exact hrun

@[deprecated xlproblemM_of_lproblemM (since := "2026-11-10")] alias reduce_loopM := xlproblemM_of_lproblemM

end Silmaril.Sim.X86.GM
