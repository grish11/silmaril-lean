module

public import Silmaril.Wasm.Cfg.MachineLProj.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd

@[expose] public section

/-!
# Native and Core control conventions agree on fitting stacks (proofs)

The logged machine `MStepL` moves between blocks with native stack conventions (`popN`, `gotoN`,
`branchN`, `ArmSel`); `MStepC` uses Core's (`popL`, `goto`, `brVals`, `topVals`, `CondArm`). They
agree when the stacks fit the block types (as typed code ensures), and only up to the values below
the branch site at function exits:

* `popN_eq_popL`, `gotoN_eq_goto`: leaving sequences, when each left level's stack has at most
  its result arity (`PopFit`);
* `branchN_block`, `branchN_loop`: a branch, when the branch-site stack has at least the label's
  arity and the frame records that arity;
* `armSel_condArm`, `labelArity_eq`: entering an arm, when the stack holds the arm's parameters
  and the block type resolves;
* `brVals_junk`: at an exit, `MStepC`'s stack is `MStepL`'s under the outer values of the frames
  left.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjC

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

theorem topVals_of_le {n : Nat} {V : List Val} (h : V.length ≤ n) : topVals n V = V := by
  simp [topVals, Nat.sub_eq_zero_of_le h]

theorem popN_eq_popL (f : Frame) :
    ∀ (k : Nat) (ls : List LFrame) (stk : List Val), PopFit f k ls stk →
      popN f k ls stk = some (popL k ls stk)
  | 0, ls, stk, _ => by simp [popN, popL]
  | _ + 1, [], _, h => h.elim
  | k + 1, L :: ls, stk, ⟨np, nr, har, hle, h⟩ => by
    simp only [popN, har, Option.bind_some, topVals_of_le hle, popL]
    exact popN_eq_popL f k ls _ h

theorem gotoN_eq_goto {t : Target} {d : Nat} {ls : List LFrame} {stk : List Val} {s : Store H}
    {f : Frame} (h : PopFit f (d - depthT t) ls stk) :
    gotoN t d ls stk s f = some (goto t d ls stk s f) := by
  simp [gotoN, goto, popN_eq_popL f _ _ _ h]

/-- **The values a branch carries are the branch-site stack over the left frames' values.** -/
theorem brVals_junk : ∀ (k : Nat) (ls : List LFrame) (stk : List Val),
    ∃ junk, brVals k ls stk = junk ++ stk
  | 0, _, stk => ⟨[], by simp [brVals]⟩
  | _ + 1, [], stk => ⟨[], by simp [brVals]⟩
  | k + 1, L :: ls, stk => by
    obtain ⟨junk, h⟩ := brVals_junk k ls (L.outer ++ stk)
    exact ⟨junk ++ L.outer, by simp [brVals, h]⟩

theorem topVals_append {n : Nat} {junk V : List Val} (h : n ≤ V.length) :
    topVals n (junk ++ V) = topVals n V := by
  simp only [topVals, List.length_append]
  rw [show junk.length + V.length - n = junk.length + (V.length - n) by omega, ← List.drop_drop,
    List.drop_left]

theorem topVals_reverse (n : Nat) (N : List Val) : topVals n N.reverse = (N.take n).reverse := by
  simp only [topVals, List.length_reverse]
  rw [List.reverse_take]

/-- **The top values a branch keeps**, native and Core, when the branch site holds them. -/
theorem topVals_brVals {n k : Nat} {ls : List LFrame} {N : List Val} (h : n ≤ N.length) :
    topVals n (brVals k ls N.reverse) = (N.take n).reverse := by
  obtain ⟨junk, hj⟩ := brVals_junk k ls N.reverse
  rw [hj, topVals_append (by simpa using h), topVals_reverse]

/-- **A branch to a `block`, `if` or `try_table` label**, native and Core: the same move, when the
frame records the result arity and the branch site holds that many values. -/
theorem branchN_block {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {np nr : Nat} (hloop : L.loop = false)
    (har : Binaryen.arity f L.bt = some (np, nr)) (hLa : L.arity = nr) (hN : nr ≤ N.length) :
    branchN body b ls k L N s f =
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - (k + 1)) (ls.drop (k + 1))
        (L.outer ++ topVals L.arity (brVals k ls N.reverse)) s f := by
  simp [branchN, har, hloop, hLa, topVals_brVals hN]

/-- **A branch to a `loop` label**, native and Core: the same re-entry, when the frame records the
parameter arity and the branch site holds that many values. -/
theorem branchN_loop {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {np nr : Nat} (hloop : L.loop = true)
    (har : Binaryen.arity f L.bt = some (np, nr)) (hLa : L.arity = np) (hN : np ≤ N.length) :
    branchN body b ls k L N s f =
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - k) (L :: ls.drop (k + 1))
        (topVals L.arity (brVals k ls N.reverse)) s f := by
  obtain ⟨a, o, lp, tt, cs, bt⟩ := L
  simp only at hloop har hLa ⊢
  subst hloop hLa
  have hlen : (N.take a).length = a := by simp; omega
  have hd : (N.take a ++ o.reverse).drop a = o.reverse := List.drop_left' hlen
  have ht : (N.take a ++ o.reverse).take a = N.take a := List.take_left' hlen
  simp only [branchN, har, Option.bind_some, ↓reduceIte, hd, ht, List.reverse_reverse,
    topVals_brVals hN]

theorem asInt_i32 {v : Val} {k : BitVec 32} (h : asInt .i32 v = some k) : v = .i32 k := by
  cases v with
  | num n =>
    obtain ⟨ty, x⟩ := n
    cases ty with
    | int it =>
      cases it with
      | i32 => simp only [asInt] at h; cases h; rfl
      | i64 => simp [asInt] at h
    | _ => simp [asInt] at h
  | _ => simp [asInt] at h

/-- **Entering an arm**, native and Core: the native split of the stack left (`ArmSel`, the top
`np` values as the arm's parameters) is Core's (`CondArm`), when the stack holds them. -/
theorem armSel_condArm {i : Instr} {V V' : List Val} {a np : Nat} (h : ArmSel i V a V')
    (hnp : np ≤ V'.length) :
    CondArm i V.reverse a (V'.drop np).reverse (V'.take np).reverse ∧
      (V'.take np).reverse.length = np := by
  have hlen : (V'.take np).reverse.length = np := by simp; omega
  have hsplit : V'.reverse = (V'.drop np).reverse ++ (V'.take np).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  refine ⟨?_, hlen⟩
  cases h with
  | plain hi => rw [hsplit]; exact .plain hi
  | @cond bt t e cv V₀ bv hb =>
    simp only [List.reverse_cons]
    rw [hsplit]
    unfold truthy at hb
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hcv := asInt_i32 hk
    subst hcv
    by_cases hk0 : k = 0
    · subst hk0
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact CondArm.ifFalse
    · have h1 : (k != 0) = true := by simpa using hk0
      simp only [h1, ↓reduceIte]
      exact CondArm.ifTrue hk0

/-- **The frame an arm entry pushes**, native and Core: the same label arity, when the block type
resolves (Core's `blockType?`, native `Binaryen.arity`). -/
theorem labelArity_eq {f : Frame} {bt : BlockType} {t₁ t₂ : List Validation.CValType} {np nr : Nat}
    (loop : Bool) (hbt : f.module.blockType? bt = some (t₁, t₂))
    (har : Binaryen.arity f bt = some (np, nr)) :
    labelArity loop t₁ t₂ = if loop then np else nr := by
  rw [MachineLFwd.arity_of_blockType hbt] at har
  simp only [Option.some.injEq, Prod.mk.injEq] at har
  obtain ⟨rfl, rfl⟩ := har
  cases loop <;> rfl

end Silmaril.Wasm.Cfg.Proofs.MachineLProjC
