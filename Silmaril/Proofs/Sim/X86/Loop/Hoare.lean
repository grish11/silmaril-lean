module

public import Silmaril.Proofs.Sim.X86.Loop.Dispatch

/-!
# The dispatcher in the every-run logic: a Wasm cut-point rule

**`dispatch_hwp`**: an invariant `I` on stores such that, from every `I`-store, the entry at
RIP evaluates (straight-line, `Silmaril.Wasm.Logic.Core.exec`) to an `I`-store, or no entry matches
and `Q` holds, gives `HWP` of `dispCode` (partial correctness, every profile and host). Solving
a Wasm problem `LProblem` of a dispatcher thus reduces to one straight-line Wasm problem per
entry (`chain_hwp` for one pass of the body).
-/

@[expose] public section

namespace Silmaril.Sim.X86.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Wp loopPost labelPost seqPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The matching entry of the chain, every run: its code runs, and `br 1` leaves the chain. -/
private theorem chain_hit_hwp {t : List (Word × List Instr)} {code : List Instr}
    {s s' : Store H} {f : Frame} {Qb : Post H} (he : exec s f [] code = some (s', f, []))
    (hq : Qb s' f (.br 0 [])) :
    HWP P host s f (vals [] ++ expression (code ++ [.br ⟨1⟩]))
      (labelPost P host 0 [] [] (seqPost P host (expression (chainCode t)) Qb)) := by
  have h := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .part) (P := P) (host := host)
    (vs := []) (rest := [.plain (.br ⟨1⟩)])
    (Q := labelPost P host 0 [] [] (seqPost P host (expression (chainCode t)) Qb)) he
    (Silmaril.Wasm.Logic.Hoare.Wp.br (m := .part) (us := []) (l := ⟨1⟩) (rest := []) hq)
  simpa [expression] using h

/-- One pass of the loop body, every run. -/
theorem chain_hwp (l : List (Word × List Instr)) {s : Store H} {f : Frame} {w : Word}
    {Qb : Post H} (hrip : gval s f .rip = some (Val.i64 w))
    (h : match lookupC l w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ Qb s' f (.br 0 [])
      | none => Qb s f (.normal [])) :
    HWP P host s f (expression (chainCode l)) Qb := by
  induction l with
  | nil =>
    exact Wp.of_vals (m := .part) (vs := []) (by simpa [lookupC] using h)
  | cons e t ih =>
    show HWP P host s f (expression (chainCode (e :: t))) Qb
    obtain ⟨a, code⟩ := e
    have hcode : expression (chainCode ((a, code) :: t)) =
        vals [] ++ expression [gget .rip, c64 a, .intRelOp .i64 .eq] ++
          (.plain (.if_ .empty (code ++ [.br ⟨1⟩]) []) :: expression (chainCode t)) := by
      simp [chainCode, entryCode, expression, vals]
    rw [hcode]
    refine Silmaril.Wasm.Examples.Common.Wp.exec (m := .part) ?_
    simp only [List.reverse_nil, Silmaril.Wasm.Logic.Core.exec_cons, exec1_gget, hrip,
      Option.map_some, exec1_c64, exec1_eq64, Silmaril.Wasm.Logic.Core.exec_nil, List.reverse_cons,
      List.nil_append, Silmaril.Wasm.Logic.Hoare.wp_part]
    refine HWP.if_ (us := []) (fun hc => ?_) (fun hc => ?_)
    · have hwa : w = a := by
        by_contra hne
        exact hc (by simp [bool32, hne])
      have hl : lookupC ((a, code) :: t) w = some code := by simp [lookupC, hwa]
      obtain ⟨s', he, hq⟩ : ∃ s', exec s f [] code = some (s', f, []) ∧ Qb s' f (.br 0 []) := by
        simpa only [hl] using h
      exact HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl (chain_hit_hwp he hq)
    · have hwa : w ≠ a := fun hwa => by simp [bool32, hwa] at hc
      have hl : lookupC ((a, code) :: t) w = lookupC t w := by simp [lookupC, hwa]
      refine HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
      exact Wp.of_vals (m := .part) (vs := []) (ih (by simpa only [hl] using h))

/-- **The dispatcher's cut-point rule** (partial correctness, every run). -/
theorem dispatch_hwp (ctab : List (Word × List Instr)) {f : Frame} (I : Store H → Prop)
    (Q : Post H)
    (hstep : ∀ s, I s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC ctab w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ I s'
      | none => Q s f (.normal []))
    {s : Store H} (hI : I s) :
    HWP P host s f (expression (dispCode ctab)) Q := by
  let Inv : Store H → Frame → List Val → Prop := fun s' f' vs => vs = [] ∧ f' = f ∧ I s'
  have h := HWP.loop (P := P) (host := host) (us := []) (Inv := Inv) (Q := Q)
    (bt := .empty) (body := chainCode ctab) (t₁ := []) (t₂ := [])
    (fun _ _ _ _ => rfl) (fun _ _ vs hi => by rw [hi.1]; rfl) ?_ (vs := []) (s := s) (f := f)
    ⟨rfl, rfl, hI⟩
  · simpa [dispCode, expression, vals] using h
  · rintro s' f' vs ⟨rfl, rfl, hI'⟩
    obtain ⟨w, hw, hm⟩ := hstep s' hI'
    refine chain_hwp ctab hw ?_
    revert hm
    cases lookupC ctab w with
    | some code =>
      rintro ⟨s'', he, hI''⟩
      exact ⟨s'', he, [], [], rfl, rfl, ⟨rfl, rfl, hI''⟩⟩
    | none => exact fun hq => hq

end Silmaril.Sim.X86.Loop
