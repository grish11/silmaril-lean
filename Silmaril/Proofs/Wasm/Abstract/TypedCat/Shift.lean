module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: **the arity check is stable under a higher
stack** (`chkE_shift`): code checked from height `h`, ending at `o`, is checked from height
`h + k`, ending at `o` shifted by `k` (a branch, `return` or never-falling-through end stays so).
Every instruction's check only asks for at least so many values; block bodies are checked at their
parameter count, independent of the outer height. With Core's `Instrs_ok/frame` this is the
**typed frame rule** (`tmor_frame`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type}

section Shift

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

theorem tableOk_shift {h k : Nat} {ls : List LabelIdx} (hc : tableOk labels h ls = true) :
    tableOk labels (h + k) ls = true := by
  simp only [tableOk, List.all_eq_true] at hc ⊢
  intro l hl
  have h1 := hc l hl
  rcases hx : labels[l.toNat]? with _ | n
  · rw [hx] at h1; cases h1
  · rw [hx] at h1
    simp only [decide_eq_true_eq] at h1 ⊢
    omega

/-- A flat instruction read through its pops and pushes. -/
theorem effShift {i : Instr} {h k : Nat} {o : Option Nat}
    (hi : ∀ h, flatChkE ext F mi nl ret labels h i =
      match flatEff F mi nl i with
      | some (p, q) => if p ≤ h then some (some (h - p + q)) else none
      | none => none)
    (hc : flatChkE ext F mi nl ret labels h i = some o) :
    flatChkE ext F mi nl ret labels (h + k) i = some (o.map (· + k)) := by
  rw [hi] at hc ⊢
  generalize flatEff F mi nl i = e at hc ⊢
  rcases e with _ | ⟨p, q⟩
  · cases hc
  · simp only at hc ⊢
    split at hc
    · cases hc
      rw [ite_eq_left (by omega), show h + k - p + q = h - p + q + k by omega]
      rfl
    · cases hc

/-- A call form, `throw` or `throw_ref` read through the extension. -/
theorem extShift {i : Instr} {h k : Nat} {o : Option Nat}
    (hi : ∀ h, flatChkE ext F mi nl ret labels h i = extStep (ext F mi i) ret h)
    (hc : flatChkE ext F mi nl ret labels h i = some o) :
    flatChkE ext F mi nl ret labels (h + k) i = some (o.map (· + k)) := by
  rw [hi] at hc ⊢
  generalize ext F mi i = e at hc ⊢
  rcases e with _ | (⟨p, q⟩ | ⟨p, r⟩ | p | ns)
  · cases hc
  · simp only [extStep] at hc ⊢
    split at hc
    · cases hc
      rw [ite_eq_left (by omega), show h + k - p + q = h - p + q + k by omega]
      rfl
    · cases hc
  · simp only [extStep] at hc ⊢
    split at hc
    · rename_i hpr
      cases hc
      rw [ite_eq_left ⟨by omega, hpr.2⟩]
      rfl
    · cases hc
  · simp only [extStep] at hc ⊢
    split at hc
    · cases hc
      rw [ite_eq_left (by omega)]
      rfl
    · cases hc
  · cases hc

theorem flatChkE_shift (k : Nat) {h : Nat} {i : Instr} {o : Option Nat}
    (hc : flatChkE ext F mi nl ret labels h i = some o) :
    flatChkE ext F mi nl ret labels (h + k) i = some (o.map (· + k)) := by
  cases i
  case unreachable => cases hc; rfl
  case br l =>
    simp only [flatChkE] at hc ⊢
    rcases hx : labels[l.toNat]? with _ | n <;> simp only [hx] at hc ⊢
    · cases hc
    · split at hc
      · cases hc
        rw [ite_eq_left (by omega)]
        rfl
      · cases hc
  case brIf l =>
    simp only [flatChkE] at hc ⊢
    rcases hx : labels[l.toNat]? with _ | n <;> simp only [hx] at hc ⊢
    · cases hc
    · split at hc
      · cases hc
        rw [ite_eq_left (by omega), show h + k - 1 = h - 1 + k by omega]
        rfl
      · cases hc
  case brTable ls d =>
    simp only [flatChkE] at hc ⊢
    split at hc
    · rename_i hcond
      cases hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have ht := tableOk_shift (k := k) hcond.2
      rw [show h - 1 + k = h + k - 1 by omega] at ht
      rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, ht⟩)]
      rfl
    · cases hc
  case return_ =>
    simp only [flatChkE] at hc ⊢
    split at hc
    · cases hc
      rw [ite_eq_left (by omega)]
      rfl
    · cases hc
  all_goals first
    | exact effShift (fun _ => rfl) hc
    | exact extShift (fun _ => rfl) hc

mutual
/-- **The check is stable under a higher stack.** -/
theorem chkE_shift (k : Nat) :
    ∀ (h : Nat) (es : List BExpr) {o : Option Nat},
      chkE ext F mi nl ret labels (some h) es = some o →
        chkE ext F mi nl ret labels (some (h + k)) es = some (o.map (· + k))
  | h, [], o, hc => by
    cases hc
    rfl
  | h, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    refine chk_consE.mpr ⟨o₁.map (· + k), chk1E_shift k h e h1, ?_⟩
    rcases o₁ with _ | h₁
    · rw [chk_noneE] at h2
      cases h2
      exact chk_noneE es
    · exact chkE_shift k h₁ es h2

theorem chk1E_shift (k : Nat) :
    ∀ (h : Nat) (e : BExpr) {o : Option Nat},
      chk1E ext F mi nl ret labels h e = some o →
        chk1E ext F mi nl ret labels (h + k) e = some (o.map (· + k))
  | h, .op i args, o, hc => by
    simp only [chk1E, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa.map (· + k), chkE_shift k h args ha, ?_⟩
    rcases oa with _ | h₁
    · cases hk
      rfl
    · exact flatChkE_shift k hk
  | h, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_blockE hc
    show chk1E ext F mi nl ret labels (h + k) (.block bt body) = some (some (h - np + nr + k))
    have hle' : np ≤ h + k := by omega
    have e : h + k - np + nr = h - np + nr + k := by omega
    simp only [chk1E, hbt, hle', decide_true, Bool.true_and, hends, ite_true, e]
  | h, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loopE hc
    show chk1E ext F mi nl ret labels (h + k) (.loop bt body) = some (some (h - np + nr + k))
    have hle' : np ≤ h + k := by omega
    have e : h + k - np + nr = h - np + nr + k := by omega
    simp only [chk1E, hbt, hle', decide_true, Bool.true_and, hends, ite_true, e]
  | h, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_ifE hc
    have hco' := chkE_shift k h c hco
    rcases oc with _ | h₁
    · simp only [chk1E, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      cases hy
      simp only [chk1E, Option.bind_eq_some_iff]
      exact ⟨none, hco', rfl⟩
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      show chk1E ext F mi nl ret labels (h + k) (.if_ bt c t el) =
        some (some (h₁ - 1 - np + nr + k))
      simp only [chk1E, Option.bind_eq_some_iff]
      refine ⟨some (h₁ + k), hco', ?_⟩
      have hle' : np + 1 ≤ h₁ + k := by omega
      have e : h₁ + k - 1 - np + nr = h₁ - 1 - np + nr + k := by omega
      simp only [hbt, hle', decide_true, ht, he, Bool.and_self, ite_true, e]
  | h, .tryTable bt cs body, o, hc => by
    simp only [chk1E] at hc ⊢
    rcases hx : ext F mi (.tryTable bt cs []) with _ | (⟨p, q⟩ | ⟨p, r⟩ | p | ns) <;>
      rcases hb : blockArity mi bt with _ | ⟨np, nr⟩ <;> simp only [hx, hb] at hc ⊢
    all_goals (try cases hc)
    split at hc
    · rename_i hcond
      cases hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hle, hok⟩, hends⟩ := hcond
      rw [ite_eq_left (by
          simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨by omega, hok⟩, hends⟩),
        show h + k - np + nr = h - np + nr + k by omega]
      rfl
    · cases hc
end

end Shift

theorem ftOut_map (ft : Bool) (n k : Nat) : (ftOut ft n).map (· + k) = ftOut ft (n + k) := by
  cases ft <;> rfl

/-- **The typed frame rule**: typed code is typed with extra value types below its stack. -/
theorem tmor_frame {Γ : Ctx H} {I J : TIface} {ft : Bool} {es : List BExpr}
    (h : TMor Γ I J ft es) {R : List CValType} (hR : ResultOk I.C.toTypeCtx R) :
    TMor Γ (I.withBelow R) (J.withBelow R) ft es := by
  obtain ⟨hm, xs, hx, hC, ht, hc⟩ := h
  refine ⟨hm, xs, hx, hC, InstrsOk.frame ht hR, ?_⟩
  have hc' : chkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels
      (some I.ts.length) es = some (ftOut ft J.ts.length) := hc
  have h2 := chkE_shift R.length I.ts.length es hc'
  rw [ftOut_map] at h2
  show chkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels
    (some (R ++ I.ts).length) es = some (ftOut ft (R ++ J.ts).length)
  rw [List.length_append, List.length_append, Nat.add_comm R.length, Nat.add_comm R.length]
  exact h2

end Silmaril.Proofs.Wasm.Abstract.TypedCat
