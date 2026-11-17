module

public import Silmaril.Proofs.Wasm.Cfg.MachineLBwd

@[expose] public section

/-!
# Pending calls of the logged machine (H2, proofs)

A pending call is encoded, as an internal witness only, by answering it with a **callee trap**:
`EvalLXPS`'s `callTrap`/`indTrap`/`refTrap` record the call with the trap answer and end the
caller at once, outside every handler. `trap_last`: a trap-answered call is the last entry of a
run's log, and the run then ends in a trap in that answer's store.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLPend

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS wasmOShape)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **The trap-answered entry** of the internal call `z` (callee, arguments, store at the call),
the trap leaving the store `s₂`. -/
def trapEntry (z : (wasmOShape H).self.Op) (s₂ : Store H) : SCall H :=
  SCall.mk z.1 z.2.1 z.2.2 (.inr ()) s₂

/-- Where an entry sits in a concatenated log. -/
theorem loc2 {l₁ l₂ A B : List (SCall H)} {x : SCall H} (h : l₁ ++ l₂ = A ++ x :: B) :
    (∃ B', l₁ = A ++ x :: B' ∧ B = B' ++ l₂) ∨ (∃ A', l₂ = A' ++ x :: B ∧ A = l₁ ++ A') := by
  rcases List.append_eq_append_iff.mp h with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
  · rcases a' with _ | ⟨y, a'⟩
    · simp at h2; exact .inr ⟨[], by simp [h2], by simp⟩
    · simp at h2; obtain ⟨rfl, rfl⟩ := h2
      exact .inr ⟨y :: a', by simp, rfl⟩
  · rcases c' with _ | ⟨y, c'⟩
    · simp at h2; obtain ⟨rfl, rfl⟩ := h2; exact .inr ⟨[], by simp, by simp⟩
    · simp at h2; obtain ⟨rfl, rfl⟩ := h2; exact .inl ⟨c', by simp, rfl⟩

theorem loc3 {l₁ l₂ A B : List (SCall H)} {x y : SCall H} (h : l₁ ++ y :: l₂ = A ++ x :: B) :
    (∃ B', l₁ = A ++ x :: B') ∨ (A = l₁ ∧ x = y ∧ B = l₂) ∨
      (∃ A', l₂ = A' ++ x :: B ∧ A = l₁ ++ y :: A') := by
  rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, h2⟩
  · exact .inl ⟨B', h1⟩
  · rcases A' with _ | ⟨z, A'⟩
    · simp at h1; obtain ⟨rfl, rfl⟩ := h1; exact .inr (.inl ⟨by simpa using h2, rfl, rfl⟩)
    · simp at h1; obtain ⟨rfl, rfl⟩ := h1; exact .inr (.inr ⟨A', rfl, h2⟩)

theorem trapEntry_ne {z : (wasmOShape H).self.Op} {s₂ s' : Store H} {a : Nat} {args : List Val}
    {s₁ : Store H} {b : List Val ⊕ Nat} : trapEntry z s₂ ≠ SCall.mk a args s₁ (.inl b) s' := by
  intro h
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp h
  have := congrArg Prod.fst (eq_of_heq h2)
  cases this

theorem trapEntry_eq {z : (wasmOShape H).self.Op} {s₂ s' : Store H} {a : Nat} {args : List Val}
    {s₁ : Store H} (h : trapEntry z s₂ = SCall.mk a args s₁ (.inr ()) s') :
    z = ⟨a, (args, s₁)⟩ ∧ s₂ = s' := by
  obtain ⟨a', args', s₁'⟩ := z
  have h1 := congrArg Sigma.fst h
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp h
  have h3 := congrArg Prod.snd (eq_of_heq h2)
  simp only [trapEntry, SCall.mk] at h1
  cases h1
  exact ⟨rfl, h3⟩

/-- **A trap-answered call ends the run**: it is the last entry of the log, and the run ends in a
trap in the answer's store. -/
theorem trap_last {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ A z s₂ B, l = A ++ trapEntry z s₂ :: B → B = [] ∧ r.1 = s₂ ∧ r.2.2 = .flow .trap := by
  induction h with
  | nil => intro A z s₂ B h; simp at h
  | argsAbort _ _ ih => exact ih
  | callRet _ _ _ _ iha ihk =>
    intro A z s₂ B h
    rcases loc3 h with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · exact ihk A' z s₂ B h1
  | callThrow _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · simp at h1
  | callTrap _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, h2⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact ⟨h2, (trapEntry_eq h1).2.symm, rfl⟩
    · simp at h1
  | opOk _ _ _ _ iha ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact ihk A' z s₂ B h1
  | opStop _ _ _ _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | blockOk _ _ hvs _ ihb ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · have := (ihb A z s₂ B' h1).2.2; simp at this; subst this; simp [Flow.blockVals] at hvs
    · exact ihk A' z s₂ B h1
  | blockBrk _ _ ihb => intro A z s₂ B h; simpa using (ihb A z s₂ B h).2.2
  | blockEsc _ _ _ ihb => exact ihb
  | loopOk _ _ _ ihb ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (ihb A z s₂ B' h1).2.2
    · exact ihk A' z s₂ B h1
  | loopBack _ _ _ ihb ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (ihb A z s₂ B' h1).2.2
    · exact ihk A' z s₂ B h1
  | loopBrk _ _ ihb => intro A z s₂ B h; simpa using (ihb A z s₂ B h).2.2
  | loopEsc _ _ _ ihb => exact ihb
  | ifOk _ _ _ _ hvs _ ihc iha ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · rcases loc2 h1 with ⟨B'', h2, -⟩ | ⟨A'', h2, -⟩
      · simpa using (ihc A z s₂ B'' h2).2.2
      · have := (iha A'' z s₂ B' h2).2.2; simp at this; subst this; simp [Flow.blockVals] at hvs
    · exact ihk A' z s₂ B h1
  | ifBrk _ _ _ _ ihc iha =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (ihc A z s₂ B' h1).2.2
    · simpa using (iha A' z s₂ B h1).2.2
  | ifEsc _ _ _ _ _ ihc iha =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (ihc A z s₂ B' h1).2.2
    · exact iha A' z s₂ B h1
  | ifAbort _ _ ihc => exact ihc
  | indRet _ _ _ _ _ _ iha ihk =>
    intro A z s₂ B h
    rcases loc3 h with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · exact ihk A' z s₂ B h1
  | indThrow _ _ _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · simp at h1
  | indTrap _ _ _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, h2⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact ⟨h2, (trapEntry_eq h1).2.symm, rfl⟩
    · simp at h1
  | indRes _ _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | refRet _ _ _ _ _ iha ihk =>
    intro A z s₂ B h
    rcases loc3 h with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · exact ihk A' z s₂ B h1
  | refThrow _ _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact absurd h1 trapEntry_ne
    · simp at h1
  | refTrap _ _ _ _ iha =>
    intro A z s₂ B h
    rcases loc3 (l₂ := []) (by simpa using h) with ⟨B', h1⟩ | ⟨-, h1, h2⟩ | ⟨A', h1, -⟩
    · simpa using (iha A z s₂ B' h1).2.2
    · exact ⟨h2, (trapEntry_eq h1).2.symm, rfl⟩
    · simp at h1
  | refNull _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | tail _ _ _ _ _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | tailRes _ _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | throw _ _ _ _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | throwRefNull _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | throwRefExn _ iha => intro A z s₂ B h; simpa using (iha A z s₂ B h).2.2
  | tryOk _ _ hvs _ ihb ihk =>
    intro A z s₂ B h
    rcases loc2 h with ⟨B', h1, -⟩ | ⟨A', h1, -⟩
    · have := (ihb A z s₂ B' h1).2.2; simp at this; subst this; simp [Flow.blockVals] at hvs
    · exact ihk A' z s₂ B h1
  | tryBrk _ _ ihb => intro A z s₂ B h; simpa using (ihb A z s₂ B h).2.2
  | tryEsc _ _ _ _ ihb => exact ihb
  | tryCatch _ _ _ ihb => intro A z s₂ B h; simpa using (ihb A z s₂ B h).2.2
  | tryRethrow _ _ _ ihb => intro A z s₂ B h; simpa using (ihb A z s₂ B h).2.2

/-! ## The encoding, both ways -/

/-- **A reached call, answered by a callee trap** (`callTrap`, `indTrap`, `refTrap`): for every
answer store `s₂`, the code runs with the prefix log then the trap-answered entry, ending in a
trap in `s₂` (in the frame at the call). -/
theorem reach_trap {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {l : List (SCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXPS s f N es l z)
    (s₂ : Store H) : ∃ f', EvalLXPS s f N es (l ++ [trapEntry z s₂]) (s₂, f', .flow .trap) := by
  induction h with
  | call hargs hfi hty => exact ⟨_, .callTrap hargs hfi hty⟩
  | ind hargs hres hfi hty hy => exact ⟨_, .indTrap hargs hres hfi hty hy⟩
  | ref hargs hfi hty hy => exact ⟨_, .refTrap hargs hfi hty hy⟩
  | args _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .argsAbort h (by simp [POut.IsNormal, Flow.IsNormal])⟩
  | callK hargs hfi hty _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.callRet hargs hfi hty h⟩
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.indRet hargs hres hfi hty hy h⟩
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.refRet hargs hfi hty hy h⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.opOk hi hargs hflat h⟩
  | block har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .blockEsc har h trivial⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.blockOk har hbody hvs h⟩
  | loop har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .loopEsc har h trivial⟩
  | loopK har hbody _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.loopOk har hbody h⟩
  | loopBack har hbody _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.loopBack har hbody h⟩
  | cond _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .ifAbort h (by simp [POut.IsNormal, Flow.IsNormal])⟩
  | arm hc hb har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.ifEsc hc hb har h trivial⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.ifOk hc hb har harm hvs h⟩
  | handler har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .tryEsc har h trivial trivial⟩
  | tryK har hbody hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.tryOk har hbody hvs h⟩

theorem singleton_eq {l₁ A : List (SCall H)} {x y : SCall H} (h : l₁ ++ [y] = A ++ [x]) :
    l₁ = A ∧ y = x := by
  simpa using List.append_inj' h rfl

/-- A run whose log holds a trap-answered entry does not end normally. -/
theorem trap_not_normal {s s' : Store H} {f f' : Frame} {N N' : List Val} {es : List BExpr}
    {A B : List (SCall H)} {z : (wasmOShape H).self.Op} {s₂ : Store H}
    (h : EvalLXPS s f N es (A ++ trapEntry z s₂ :: B) (s', f', .flow (.normal N'))) : False := by
  simpa using (trap_last h A z s₂ B rfl).2.2

/-- **A run ending with a trap-answered entry reached that call** after exactly the prefix
log. -/
theorem trap_reach {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ (l' : List (SCall H)) (z : (wasmOShape H).self.Op) (s₂ : Store H),
      l = l' ++ [trapEntry z s₂] → ReachLXPS s f N es l' z := by
  induction h with
  | nil => intro l' z s₂ h; simp at h
  | argsAbort _ _ ih => intro l' z s₂ h; exact .args (ih l' z s₂ h)
  | callRet hargs hfi hty _ _ ihk =>
    intro l' z s₂ h
    rcases loc3 h.symm with ⟨B', h1⟩ | ⟨-, h1, -⟩ | ⟨A', h1, h2⟩
    · simp at h1
    · sorry
    · sorry
  | _ => sorry

end Silmaril.Wasm.Cfg.Proofs.MachineLPend
