module

public import Silmaril.Wasm.Abstract.HostTrapS.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Games.Abstract.ModuleTrap.Thms
public import Silmaril.Proofs.Wasm.Abstract.HostTrapS.Runs

/-!
# Host traps end the native Wasm session round (proofs)

* `wasmHOpenXPS_trapAborts`: in the session open module, a trapped call (a host call answered
  `Result.trap`, or an internal call answered by a trap) is the last call, and the function ends
  in a trap keeping its store: a Wasm body by `evalLXPS_trapLast`, a pending tail call by
  `tailAnsS`, a host function by `resFlow .trap = .trap`.
* `wasmHOpenXP_trapAborts`: in the canonical open module, a host call answered `Result.trap` is
  the only call of a host function, which ends `.trap`; Wasm bodies record internal calls only,
  answered by returns, never trapped.
* `wasmEvFunXPS_trapAborts`, `wasmEvFunXP_trapAborts`: hence so are the closures
  (`Shape.close_trapAborts`).
* `wasmEvFunDXP_div_noTrap`, `pendLXP_noTrap`, `wasmEvInfNXP_noTrap`: no divergent behaviour, no
  pending call and no productive stream of the canonical closure has a host trap.
* `sessionTripleXP_trapAbortsRound`: the session triple aborts every round at a host trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostTrapS

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## The open modules -/

/-- **In the session open module, a trapped call ends the function with a trap.** -/
theorem wasmHOpenXPS_trapAborts :
    OpenTrapAborts IsHostTrap (trapEndS H) (wasmHOpenXPS (H := H)) := by
  intro a s vs x hx
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, -, -, -, hrun, hex, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, -, -, -, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, -, -, -, hex, rfl⟩
  · refine TrapLast.mono (evalLXPS_trapLast hrun) fun h => ?_
    cases h
    simp only [exitFlow, Option.some.injEq] at hex
    subst hex
    exact trivial
  · refine trapLast_concat (noTrap (evalLXPS_trapLast hrun) (by simp)) fun h => ?_
    rcases b with b | ⟨⟩
    · exact absurd h not_ps_mk_inl
    · exact trivial
  · refine trapLast_singleton fun h => ?_
    change r = .trap at h
    subst h
    simp only [resFlow, exitFlow, Option.some.injEq] at hex
    subst hex
    exact trivial

theorem not_trapCall_lift (o : OCall H) :
    ¬ TrapCall (sh := wasmHShape H) IsHostTrap (trapEndH H) o.lift := by
  rcases o with ⟨⟨⟨⟩⟩ | y, b, s'⟩
  intro h
  cases h

theorem not_trapCall_map_lift (l : List (OCall H)) :
    ∀ x ∈ l.map OCall.lift, ¬ TrapCall (sh := wasmHShape H) IsHostTrap (trapEndH H) x := by
  intro x hx
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
  exact not_trapCall_lift o

/-- **In the canonical open module, a host trap is the last call, and the function traps.** -/
theorem wasmHOpenXP_trapAborts :
    OpenTrapAborts IsHostTrap (trapEndH H) (wasmHOpenXP (H := H)) := by
  intro a s vs x hx
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, -, -, -, -, -, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, -, -, -, -, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, -, -, -, hex, rfl⟩
  · exact trapLast_of_forall (not_trapCall_map_lift l)
  · exact trapLast_of_forall (not_trapCall_map_lift _)
  · refine trapLast_singleton fun h => ?_
    change r = .trap at h
    subst h
    simp only [resFlow, exitFlow, Option.some.injEq] at hex
    subst hex
    rfl

theorem trapEndS_trap (g : (wasmHShapeS H).F) : trapEndS H g .trap := trivial

theorem not_trapEndS_div (g : (wasmHShapeS H).F) : ¬ trapEndS H g .div := fun h => h

theorem trapEndH_trap (g : (wasmHShape H).F) : trapEndH H g .trap := rfl

theorem not_trapEndH_div (g : (wasmHShape H).F) : ¬ trapEndH H g .div := fun h => by cases h

/-! ## The closures -/

theorem wasmEvFunXPS_trapAborts :
    ClosedTrapAborts IsHostTrap (trapEndS H) (Shape.close (wasmHOpenXPS (H := H))) :=
  close_trapAborts wasmHOpenXPS_trapAborts trapEndS_trap not_trapEndS_div

theorem wasmEvFunXP_trapAborts :
    ClosedTrapAborts IsHostTrap (trapEndH H) (Shape.close (wasmHOpenXP (H := H))) :=
  close_trapAborts wasmHOpenXP_trapAborts trapEndH_trap not_trapEndH_div

/-- **A divergent canonical behaviour has no host trap.** -/
theorem wasmEvFunDXP_div_noTrap {s : Store H} {p : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunDXP s p) :
    ∀ e ∈ cs, ¬ IsHostTrap e.1 e.2 := by
  refine closeDLog_div_noTrap wasmHOpenXP_trapAborts trapEndH_trap not_trapEndH_div ?_ h rfl
  rintro z u ⟨fi, fn, l, -, -, -, rfl⟩
  exact not_trapCall_map_lift l

/-- **No canonical pending call follows a host trap.** -/
theorem pendLXP_noTrap {s : Store H} {a : Nat} {vs : List Val}
    {q : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (h : PendLXP s a vs q m) :
    ∀ e ∈ q, ¬ IsHostTrap e.1 e.2 := by
  induction h with
  | self => simp
  | @desc s a vs fi fn l q q' z m _ _ _ hq _ ih =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact substPre_noTrap wasmEvFunXP_trapAborts hq (not_trapCall_map_lift l) e he
    · exact ih e he
  | @tail s s₁ a vs fi fn f₂ a' n args l q q' m _ _ _ hq _ ih =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact substPre_noTrap wasmEvFunXP_trapAborts hq (not_trapCall_map_lift l) e he
    · exact ih e he

/-- **No productive canonical stream has a host trap.** -/
theorem wasmEvInfNXP_noTrap {s : Store H} {p : Nat × List Val} {ω : Nat → Call (wasmHostSig H)}
    (h : ω ∈ wasmEvInfNXP s p) (k : Nat) : ¬ IsHostTrap (ω k).1 (ω k).2 := by
  refine closeInfL_noTrap wasmHOpenXP_trapAborts trapEndH_trap not_trapEndH_div ?_ h k
  rintro f s a ν ⟨fi, fn, ω, -, -, -, rfl⟩ i
  exact not_trapCall_lift (ω i)

/-! ## The session triple -/

/-- **The native session triple aborts every round at a host trap.** -/
theorem sessionTripleXP_trapAbortsRound :
    TrapAbortsRound IsHostTrap (sessionTripleXP (H := H)) where
  beh s a c m n d e hT hy := by
    rcases hy with hy | ⟨-, hy⟩
    · exact wasmEvFunXPS_trapAborts a.1 s a.2 _ hy c ⟨m, n⟩ d rfl hT
    · exact absurd hT (wasmEvFunDXP_div_noTrap hy ⟨m, n⟩ (by simp))
  pend s a c m n d m' hT hp := by
    have hp' : (c ++ ⟨m, n⟩ :: d, m') ∈ wasmEvPendXP s a := by
      rw [← wasmEvPendXPS_eq]
      exact hp
    exact pendLXP_noTrap hp' ⟨m, n⟩ (by simp) hT
  inf s a ω hω k := wasmEvInfNXP_noTrap hω k

end Silmaril.Proofs.Wasm.Abstract.HostTrapS
