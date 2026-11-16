module

public import Silmaril.Proofs.Sim.X86.G.Sound
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Examples.Common.Thms

/-!
# The G simulator: programs and the transfer theorem

* `emitProg_sound`: a straight-line x86 program translated method by method (P-inline)
  evaluates, from any store encoding `σ`, to a store encoding the result of `runExt`.
* `emitProg_twp`: hence the Wasm code terminates in every run (`TWP`), at every profile and for
  every host relation, ending in such a store.
* **`hwp_transfer`**: any every-run (`HWP`) property of the Wasm code holds at the store reached
  from an encoding of `σ`, which encodes the x86 result: Wasm facts become x86 facts.
* `enc_encStore`: the concrete store `encStore σ` encodes `σ`, so that a Wasm property
  quantified over encoding stores can be instantiated at every x86 state.
* **`xproblem_of_wproblem`**: the problem reduction for register properties: a Wasm problem (`WProblem`)
  about the generated code over the register globals implies the x86 problem (`XProblem`)
  about `runExt`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec_append exec_nil Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP TWP)
open Silmaril.X86 (Reg State)

variable {H : Type} {s : Store H} {f : Frame}

/-- **Soundness of a translated program.** -/
theorem emitProg_sound {p : XProg} {code : List Instr} (hc : emitProg p = some code) {σ σ' : State}
    (hE : Enc s f σ) {m m' : Silmaril.Process.Memory} (hx : runExt p σ m = some (σ', m')) :
    m' = m ∧ ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ Frames s s' f := by
  induction p generalizing s σ m code with
  | nil =>
    simp only [emitProg, Option.some.injEq, runExt, Prod.mk.injEq] at hc hx
    obtain ⟨rfl, rfl⟩ := hx
    subst hc
    exact ⟨rfl, s, rfl, hE, Frames.refl s f⟩
  | cons x p ih =>
    obtain ⟨i, n⟩ := x
    simp only [emitProg, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hc
    obtain ⟨c₁, h₁, cs, h₂, rfl⟩ := hc
    simp only [runExt] at hx
    split at hx
    · rename_i σ₁ m₁ hx₁
      obtain ⟨rfl, s₁, he₁, hE₁, hF₁⟩ := emit_sound h₁ hE hx₁
      obtain ⟨rfl, s₂, he₂, hE₂, hF₂⟩ := ih h₂ hE₁ hx
      exact ⟨rfl, s₂, by rw [exec_append, he₁]; exact he₂, hE₂, hF₁.trans hF₂⟩
    · cases hx

variable {P : Profile} {host : HostSemantics H}

/-- The translated program **terminates in every run**, at every profile and for every host,
in a store encoding the x86 result. -/
theorem emitProg_twp {p : XProg} {code : List Instr} (hc : emitProg p = some code) {σ σ' : State}
    (hE : Enc s f σ) {m m' : Silmaril.Process.Memory} (hx : runExt p σ m = some (σ', m')) :
    TWP P host s f (expression code)
      (fun s' f' o => o = .normal [] ∧ f' = f ∧ Enc s' f σ' ∧ Frames s s' f) := by
  obtain ⟨-, s', he, hE', hF⟩ := emitProg_sound hc hE hx
  let Q : Post H := fun s'' f' o => o = .normal [] ∧ f' = f ∧ Enc s'' f σ' ∧ Frames s s'' f
  have hq : Q s' f (.normal []) := ⟨rfl, rfl, hE', hF⟩
  have h := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .total) (P := P) (host := host)
    (s := s) (f := f) (vs := []) (rest := []) (Q := Q) he
    (Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .total) (P := P) (host := host) hq)
  simpa [vals] using h

/-- **The transfer theorem.** Every-run Wasm facts about the translated program are facts about
the x86 run: if the Wasm code satisfies `Q` in every run from a store encoding `σ`, then `Q`
holds at a store encoding the x86 result `σ'` (reached by a run of the code). -/
theorem hwp_transfer {p : XProg} {code : List Instr} (hc : emitProg p = some code) {σ σ' : State}
    (hE : Enc s f σ) {m m' : Silmaril.Process.Memory} (hx : runExt p σ m = some (σ', m'))
    {Q : Post H} (hW : HWP P host s f (expression code) Q) :
    ∃ s', Enc s' f σ' ∧ Frames s s' f ∧ Q s' f (.normal []) := by
  obtain ⟨-, s', he, hE', hF⟩ := emitProg_sound hc hE hx
  have hs := Silmaril.Wasm.Logic.Core.exec_sound (P := P) (host := host) (rest := []) he
  simp only [List.reverse_nil, List.append_nil] at hs
  exact ⟨s', hE', hF, Silmaril.Wasm.Logic.Hoare.HWP.sound_vals hW (by simpa [vals] using hs)⟩

/-! ## A store encoding any state -/

theorem Loc.idx_inj (l₁ l₂ : Loc) (h : l₁.idx = l₂.idx) : l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> simp only [Loc.idx, reduceCtorEq] at h ⊢ <;>
    first
    | (rename_i r q; exact congrArg _ (Reg.toBitVec_injective (BitVec.eq_of_toNat_eq h)))
    | (rename_i r; have := r.toBitVec.isLt; omega)
    | omega

theorem gval_encStore (σ : State) (l : Loc) :
    gval (encStore (H := H) σ) encFrame l = some (Val.i64 (encVal σ ⟨l.idx, l.idx_lt⟩)) := by
  rw [gval_eq]
  simp only [encFrame]
  rw [List.getElem?_range l.idx_lt, Option.bind_some, encStore, List.getElem?_ofFn]
  simp only [l.idx_lt, dite_true]
  rfl

theorem enc_encStore (σ : State) : Enc (encStore (H := H) σ) encFrame σ := by
  have flag : ∀ o : Option Bool, FlagEnc (some (Val.i64 (b64 (o.getD false)))) o := fun o =>
    ⟨o.getD false, rfl, by cases o <;> simp [Silmaril.X86.FlagValue.Admits]⟩
  refine ⟨⟨fun l => ⟨l.idx, by simp [encFrame, l.idx_lt], by simp [encStore, l.idx_lt]⟩,
    fun l₁ l₂ a h₁ h₂ => Loc.idx_inj _ _ ?_⟩, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [encFrame, List.getElem?_range l₁.idx_lt, List.getElem?_range l₂.idx_lt,
      Option.some.injEq] at h₁ h₂
    omega
  all_goals rw [gval_encStore]
  · have : r.toBitVec.toNat < 16 := r.toBitVec.isLt
    simp only [Loc.idx, encVal, this, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Reg.ofBitVec_toBitVec]
  all_goals simp only [Loc.idx, encVal]; first | rfl | exact flag _

/-! ## The problem reduction for register properties -/

theorem Enc.gregs {σ : State} (h : Enc s f σ) : GRegs s f σ.read :=
  ⟨h.1, h.2.1, ⟨_, h.2.2.1⟩, (h.2.2.2.1.imp fun _ h => h.1), (h.2.2.2.2.1.imp fun _ h => h.1),
    (h.2.2.2.2.2.1.imp fun _ h => h.1), (h.2.2.2.2.2.2.imp fun _ h => h.1)⟩

/-- **The reduction**: solving the Wasm problem for the translated code (at any one profile and
host relation) solves the x86 problem. -/
theorem xproblem_of_wproblem {p : XProg} {code : List Instr} (hc : emitProg p = some code)
    {Pre : (Reg → BitVec 64) → Prop} {Post : (Reg → BitVec 64) → (Reg → BitVec 64) → Prop}
    (hW : WProblem (H := H) P host code Pre Post) : XProblem p Pre Post := by
  intro σ σ' m m' hpre hx
  have hE := enc_encStore (H := H) σ
  obtain ⟨s', hE', -, -, hq⟩ := hwp_transfer (P := P) (host := host) hc hE hx
    (hW _ _ σ.read hE.gregs hpre)
  exact hq σ'.read hE'.2.1

@[deprecated hwp_transfer (since := "2026-11-10")] alias transfer := hwp_transfer

@[deprecated xproblem_of_wproblem (since := "2026-11-10")] alias reduce := xproblem_of_wproblem

end Silmaril.Sim.X86.G
