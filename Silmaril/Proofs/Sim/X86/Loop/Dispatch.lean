module

public import Silmaril.Sim.X86.Loop.Defs
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# The dispatcher: total correctness from x86 runs, and the reduction

* `chain_twp`: one pass of the dispatcher's loop body, given what the entry at RIP does;
* **`dispatch_twp`**: a cut-point rule for the dispatcher (total correctness, every profile and
  host): a measured invariant `J k` on stores, re-established by every entry at a smaller
  measure, gives `TWP` of `dispCode` with the exit condition;
* `tsafe_run`: a totally correct configuration has a run to an exit satisfying the
  postcondition;
* `xrun_twp`: an `XRun` of the table from a state the store encodes is matched by every run of
  the dispatcher (`TWP`) ending in a store encoding the final state;
* **`xlproblem_of_lproblem`**: `LProblem` (Wasm, partial correctness) of `dispCode (compileTab tab)`
  solves `XLProblem tab`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP TWP TSafe Wp loopPostT labelPostT seqPostT)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem exec1_eq64 (s : Store H) (f : Frame) (rs : List Val) (x y : BitVec 64) :
    Silmaril.Wasm.Logic.Core.exec1 s f (Val.i64 y :: Val.i64 x :: rs) (.intRelOp .i64 .eq) =
      some (s, f, Val.i32 (bool32 (x == y)) :: rs) := rfl

/-- The code of one more entry of the dispatcher's chain: compare RIP with the entry's
address, and run the entry's code (then leave the chain) if they are equal. -/
private theorem expression_chainCode_cons (a : Word) (code : List Instr) (t : List (Word × List Instr)) :
    expression (chainCode ((a, code) :: t)) =
      vals [] ++ expression [gget .rip, c64 a, .intRelOp .i64 .eq] ++
        (.plain (.if_ .empty (code ++ [.br ⟨1⟩]) []) :: expression (chainCode t)) := by
  simp [chainCode, entryCode, expression, vals]

/-- The matching entry of the chain: its code runs, and `br 1` leaves the chain. -/
private theorem chain_hit_twp {t : List (Word × List Instr)} {code : List Instr}
    {s s' : Store H} {f : Frame} {Qb : Post H} (he : exec s f [] code = some (s', f, []))
    (hq : Qb s' f (.br 0 [])) :
    TWP P host s f (vals [] ++ expression (code ++ [.br ⟨1⟩]))
      (labelPostT P host 0 [] [] (seqPostT P host (expression (chainCode t)) Qb)) := by
  have h := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .total) (P := P) (host := host)
    (vs := []) (rest := [.plain (.br ⟨1⟩)])
    (Q := labelPostT P host 0 [] [] (seqPostT P host (expression (chainCode t)) Qb)) he
    (Silmaril.Wasm.Logic.Hoare.Wp.br (m := .total) (us := []) (l := ⟨1⟩) (rest := []) hq)
  simpa [expression] using h

/-- **One pass of the loop body** of the dispatcher. -/
theorem chain_twp (l : List (Word × List Instr)) {s : Store H} {f : Frame} {w : Word}
    {Qb : Post H} (hrip : gval s f .rip = some (Val.i64 w))
    (h : match lookupC l w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ Qb s' f (.br 0 [])
      | none => Qb s f (.normal [])) :
    TWP P host s f (expression (chainCode l)) Qb := by
  induction l with
  | nil =>
    exact Wp.of_vals (m := .total) (vs := []) (by simpa [lookupC] using h)
  | cons e t ih =>
    show TWP P host s f (expression (chainCode (e :: t))) Qb
    obtain ⟨a, code⟩ := e
    rw [expression_chainCode_cons]
    refine Silmaril.Wasm.Examples.Common.Wp.exec (m := .total) ?_
    simp only [List.reverse_nil, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hrip,
      Option.map_some, exec1_c64, exec1_eq64, Silmaril.Wasm.Logic.Core.exec_nil, List.reverse_cons,
      List.nil_append, Silmaril.Wasm.Logic.Hoare.wp_total]
    refine TWP.if_ (us := []) ?_
    by_cases hwa : w = a
    · have hl : lookupC ((a, code) :: t) w = some code := by simp [lookupC, hwa]
      obtain ⟨s', he, hq⟩ : ∃ s', exec s f [] code = some (s', f, []) ∧ Qb s' f (.br 0 []) := by
        simpa only [hl] using h
      have hc : bool32 (w == a) ≠ 0 := by simp [bool32, hwa]
      simp only [hc, ne_eq, not_false_eq_true, ite_true]
      exact TWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl (chain_hit_twp he hq)
    · have hl : lookupC ((a, code) :: t) w = lookupC t w := by simp [lookupC, hwa]
      have hc : bool32 (w == a) = 0 := by simp [bool32, hwa]
      simp only [hc, ne_eq, not_true_eq_false, ite_false]
      refine TWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
      exact Wp.of_vals (m := .total) (vs := []) (ih (by simpa only [hl] using h))

open Classical in
/-- The least measure of a store. -/
noncomputable def measureOf (J : Nat → Store H → Prop) (s : Store H) : Nat :=
  if h : ∃ k, J k s then Nat.find h else 0

/-- **The dispatcher's cut-point rule** (total correctness): a measured invariant `J`, such that
from every `J k`-store the entry at RIP evaluates to a `J k'`-store with `k' < k`, or no entry
matches and the exit condition `Q` holds. -/
theorem dispatch_twp (ctab : List (Word × List Instr)) {f : Frame} (J : Nat → Store H → Prop)
    (Q : Post H)
    (hstep : ∀ k s, J k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC ctab w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, J k' s'
      | none => Q s f (.normal []))
    {k : Nat} {s : Store H} (hJ : J k s) :
    TWP P host s f (expression (dispCode ctab)) Q := by
  classical
  let Inv : Store H → Frame → List Val → Prop := fun s' f' vs => vs = [] ∧ f' = f ∧ ∃ k, J k s'
  let V : Store H → Frame → List Val → Nat := fun s' _ _ => measureOf J s'
  have hmin : ∀ s', (h : ∃ k, J k s') → J (measureOf J s') s' := fun s' h => by
    simp only [measureOf, h, dite_true]; exact Nat.find_spec h
  have hle : ∀ s' k, J k s' → measureOf J s' ≤ k := fun s' k h => by
    simp only [measureOf, show ∃ k, J k s' from ⟨k, h⟩, dite_true]; exact Nat.find_min' _ h
  have hbody : ∀ s' f' vs, Inv s' f' vs → TWP P host s' f' (vals vs ++ expression (chainCode ctab))
      (Silmaril.Wasm.Logic.Hoare.loopPostT 0 [] Inv V (V s' f' vs) Q) := by
    rintro s' f' vs ⟨rfl, rfl, k', hk'⟩
    obtain ⟨w, hw, hm⟩ := hstep _ s' (hmin s' ⟨k', hk'⟩)
    refine chain_twp ctab hw ?_
    revert hm
    cases lookupC ctab w with
    | some code =>
      rintro ⟨s'', he, k'', hlt, hJ''⟩
      exact ⟨s'', he, [], [], rfl, rfl, ⟨rfl, rfl, k'', hJ''⟩,
        Nat.lt_of_le_of_lt (hle s'' k'' hJ'') hlt⟩
    | none => exact fun hq => hq
  have h : TWP P host s f (vals ([] ++ []) ++ [.plain (.loop .empty (chainCode ctab))]) Q :=
    TWP.loop (P := P) (host := host) (us := []) (Inv := Inv) (V := V) (Q := Q)
      (bt := .empty) (body := chainCode ctab) (t₁ := []) (t₂ := [])
      (fun _ _ _ _ => rfl) (fun _ _ vs hi => by rw [hi.1]; rfl) hbody ⟨rfl, rfl, k, hJ⟩
  simpa [dispCode, expression, vals] using h

/-- A totally correct configuration has a run to an exit satisfying the postcondition. -/
theorem tsafe_run {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Silmaril.Wasm.Logic.Hoare.Exits o c'.code ∧
      Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hex _ ih =>
    obtain ⟨c', hc'⟩ := hex
    obtain ⟨c'', hs, h⟩ := ih c' hc'
    exact ⟨c'', .head hc' hs, h⟩

theorem lookup_compile {tab : XTab} (hs : Supported tab) {w : Word} :
    match lookupI tab w with
    | some (i, n) => ∃ code, lookupC (compileTab tab) w = some code ∧ emitX i n = some code
    | none => lookupC (compileTab tab) w = none := by
  induction tab with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨a, i, n⟩ := e
    have ht : Supported t := fun e he => hs e (List.mem_cons_of_mem _ he)
    by_cases hwa : w = a
    · obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp (hs (a, i, n) (by simp))
      simp only [lookupI, hwa, ite_true, compileTab, List.map_cons, lookupC]
      exact ⟨code, by simp [hcode], hcode⟩
    · simp only [lookupI, hwa, ite_false, compileTab, List.map_cons, lookupC]
      exact ih ht

/-- **An x86 run is matched by the dispatcher** (every run, total correctness): from a store
encoding `σ`, every run of `dispCode (compileTab tab)` terminates, falling through with a store
encoding the final state. -/
theorem xrun_twp {tab : XTab} (hs : Supported tab) {m : Silmaril.Process.Memory} {k : Nat}
    {σ σ' : State} (hx : XRun tab m k σ σ') {s : Store H} {f : Frame} (hE : Enc s f σ) :
    TWP P host s f (expression (dispCode (compileTab tab)))
      (fun s' f' o => o = .normal [] ∧ f' = f ∧ Enc s' f σ') := by
  refine dispatch_twp (compileTab tab) (fun k s => ∃ σ, Enc s f σ ∧ XRun tab m k σ σ') _ ?_
    ⟨σ, hE, hx⟩
  rintro k s ⟨σ, hE, hx⟩
  refine ⟨σ.rip, hE.2.2.1, ?_⟩
  have hl := lookup_compile hs (w := σ.rip)
  cases hx with
  | done hn =>
    rw [hn] at hl
    rw [hl]
    exact ⟨rfl, rfl, hE⟩
  | step hi he hr =>
    rw [hi] at hl
    obtain ⟨code, hc, hcode⟩ := hl
    rw [hc]
    obtain ⟨-, s', hex, hE', -⟩ := emitX_sound hcode hE he
    exact ⟨s', hex, _, Nat.lt_succ_self _, _, hE', hr⟩

/-- **The reduction with control flow**: solving the Wasm problem of the dispatcher (at any one
profile and host relation) solves the x86 problem of the table. -/
theorem xlproblem_of_lproblem {tab : XTab} (hs : Supported tab) {Pre : (Reg → Word) → Word → Prop}
    {Post : (Reg → Word) → Word → (Reg → Word) → Word → Prop}
    (hW : LProblem (H := H) P host (dispCode (compileTab tab)) Pre Post) :
    XLProblem tab Pre Post := by
  intro σ σ' m k hpre hx
  have hE := enc_encStore (H := H) σ
  obtain ⟨⟨s', f', c'⟩, hsteps, o, hexit, rfl, rfl, hE'⟩ :=
    tsafe_run (xrun_twp (P := P) (host := host) hs hx hE)
  have hc : c' = vals [] := hexit
  subst hc
  have hH := hW _ _ σ.read σ.rip hE.gregs hE.2.2.1 hpre
  obtain ⟨-, hpost⟩ := HWP.sound_vals hH hsteps
  exact hpost σ'.read σ'.rip hE'.2.1 hE'.2.2.1

@[deprecated xlproblem_of_lproblem (since := "2026-11-10")] alias reduce_loop := xlproblem_of_lproblem

end Silmaril.Sim.X86.Loop
