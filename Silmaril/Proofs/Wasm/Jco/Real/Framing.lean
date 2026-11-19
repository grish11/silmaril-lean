module

public import Silmaril.Proofs.Wasm.Jco.Real.Mem
public import Silmaril.Wasm.Jco.Real.StepX.Defs
public import Silmaril.Wasm.Jco.Styles.Realloc.Thms

/-!
# Well-typed adaptor code runs on its own operand stack

For code that `tyExec` accepts from stack types `ts`, a returned run from an operand stack
`a ++ st` (with `a` of types `ts`) never reads `st`: it ends in `a' ++ st`, with `a'` of the
types `tyExec` computes, and the same run exists from `a ++ st'` for every `st'` (`exec_frame`).
This is what lets an `if` branch, which `XInstr.step` runs on the whole operand stack, be read as
a Wasm block, which runs on an empty one. It needs the result types of the calls
(`CallsTyped`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm (NumType)

/-! ## Building returned runs -/

theorem ok_bind_intro {σ α β : Type} {m : RM σ α} {k : α → RM σ β} {s s₁ s₂ : σ} {a : α} {b : β}
    (h₁ : m s (.ok a s₁)) (h₂ : k a s₁ (.ok b s₂)) : (m >>= k) s (.ok b s₂) :=
  (RM.bind_apply m k s _).mpr (.inl ⟨a, s₁, h₁, h₂⟩)

theorem ok_pure_intro {σ α : Type} (a : α) (s : σ) : (pure a : RM σ α) s (.ok a s) := rfl

theorem ok_ofOption_intro {σ α : Type} {x : Option α} {a : α} (h : x = some a) (s : σ) :
    (RM.ofOption x : RM σ α) s (.ok a s) := by
  subst h; rfl

/-! ## Typing facts -/

theorem asI32?_of_type {v : Flat} (h : v.type = tI32) : asI32? v = some (v.bits.cast (by rw [h]; rfl)) := by
  rcases v with ⟨t, b⟩
  simp only at h
  subst h
  rfl

theorem exists_asI32 {v : Flat} (h : v.type = tI32) : ∃ x, asI32? v = some x :=
  ⟨_, asI32?_of_type h⟩

variable (M : CoreInst) (rt : String → List NumType) (lt : List NumType)

/-- The conclusion of the framing lemmas. -/
def FrameOK (run : Silmaril.Wasm.Jco.Frame → RM M.St Silmaril.Wasm.Jco.Frame) (ls a st : List Flat)
    (ts' : List NumType) (s s' : M.St) (f' : Silmaril.Wasm.Jco.Frame) : Prop :=
  ∃ ls' a', f' = ⟨ls', a' ++ st⟩ ∧ ls'.map (·.type) = lt ∧ a'.map (·.type) = ts' ∧
    ∀ st', run ⟨ls, a ++ st'⟩ s (.ok ⟨ls', a' ++ st'⟩ s')

variable {M rt lt}

theorem typesOK_take {a : List Flat} {ts : List NumType} (ha : a.map (·.type) = ts) {n : Nat}
    (hn : n ≤ ts.length) (st : List Flat) : (a ++ st).take n = a.take n ∧
      (a ++ st).drop n = a.drop n ++ st ∧ n ≤ (a ++ st).length ∧ n ≤ a.length := by
  have hl : a.length = ts.length := by rw [← ha, List.length_map]
  refine ⟨List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    by simp; omega, by omega⟩

mutual

/-- **Framing, one instruction.** -/
theorem step_frame (hC : CallsTyped M rt) : ∀ (i : XInstr) {ts ts' : List NumType},
    tyStep rt lt i ts = some ts' →
    ∀ {ls a st : List Flat} {s s' : M.St} {f' : Silmaril.Wasm.Jco.Frame},
    ls.map (·.type) = lt → a.map (·.type) = ts →
    i.step M ⟨ls, a ++ st⟩ s (.ok f' s') → FrameOK M lt (i.step M) ls a st ts' s s' f'
  | .base (.localGet j), ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    simp only [XInstr.step, AInstr.step] at h
    rcases hv : ls[j]? with _ | v <;> simp only [hv] at h
    · cases h
    · obtain ⟨rfl, rfl⟩ := ok_pure h
      have hlt : lt[j]? = some v.type := by rw [← hls]; simp [hv]
      simp only [tyStep, hlt] at hty
      split at hty
      · simp only [Option.map_some, Option.some.injEq] at hty
        subst hty
        refine ⟨ls, v :: a, rfl, hls, by simp [ha], fun st' => ?_⟩
        simp only [XInstr.step, AInstr.step, hv]
        rfl
      · cases hty
  | .base (.localSet j), ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨v, a⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, ts⟩
      · simp at ha
      · simp only [List.map_cons, List.cons.injEq] at ha
        obtain ⟨rfl, ha⟩ := ha
        simp only [tyStep] at hty
        split at hty
        · rename_i hc
          cases hty
          simp only [List.cons_append, XInstr.step, AInstr.step] at h
          by_cases hj : j < ls.length
          · simp only [hj, ↓reduceIte] at h
            obtain ⟨rfl, rfl⟩ := ok_pure h
            refine ⟨ls.set j v, a, rfl, ?_, ha, fun st' => ?_⟩
            · rw [List.map_set, hls]
              have h2 := hc.2
              rw [List.getElem?_eq_some_iff] at h2
              obtain ⟨_, h3⟩ := h2
              rw [← h3]; exact List.set_getElem_self _
            · simp only [List.cons_append, XInstr.step, AInstr.step, hj, ↓reduceIte]; rfl
          · simp only [hj, ↓reduceIte] at h; cases h
        · cases hty
  | .base (.i32Const c), ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    simp only [tyStep, Option.some.injEq] at hty
    subst hty
    simp only [XInstr.step, AInstr.step] at h
    obtain ⟨rfl, rfl⟩ := ok_pure h
    exact ⟨ls, Flat.i32 c :: a, rfl, hls, by simp [ha], fun st' => rfl⟩
  | .base (.call g n), ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    simp only [tyStep] at hty
    split at hty
    · rename_i hn
      cases hty
      obtain ⟨ht, hd, hle, hle'⟩ := typesOK_take ha hn st
      simp only [XInstr.step, AInstr.step, hle, ↓reduceIte, ht] at h
      obtain ⟨rs, s₁, hc, hp⟩ := ok_bind h
      obtain ⟨rfl, rfl⟩ := ok_pure hp
      refine ⟨ls, rs.reverse ++ a.drop n, by simp [hd], hls, ?_, fun st' => ?_⟩
      · have := hC _ _ _ _ _ hc
        simp [List.map_reverse, this, ← ha, List.map_drop]
      · obtain ⟨ht', hd', hle₂, -⟩ := typesOK_take ha hn st'
        simp only [XInstr.step, AInstr.step, hle₂, ↓reduceIte, ht', hd']
        exact ok_bind_intro hc (by simp; rfl)
    · cases hty
  | .i32Eqz, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨v, a⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, ts⟩
      · simp at ha
      · simp only [List.map_cons, List.cons.injEq] at ha
        obtain ⟨rfl, ha⟩ := ha
        simp only [tyStep] at hty
        split at hty
        · rename_i hc
          cases hty
          simp only [List.cons_append, XInstr.step] at h
          obtain ⟨x', s₁, hx', hp⟩ := ok_bind h
          obtain ⟨hx'', rfl⟩ := ok_ofOption hx'
          obtain ⟨rfl, rfl⟩ := ok_pure hp
          refine ⟨ls, _ :: a, rfl, hls, by simp [ha], fun st' => ?_⟩
          simp only [List.cons_append, XInstr.step]
          exact ok_bind_intro (ok_ofOption_intro hx'' _) rfl
        · cases hty
  | .i32LtU, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨vb, _ | ⟨va, a⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · cases hty
        simp only [List.cons_append, XInstr.step] at h
        obtain ⟨b, s₁, hb, h₁⟩ := ok_bind h
        obtain ⟨hb', rfl⟩ := ok_ofOption hb
        obtain ⟨x, s₂, hx, hp⟩ := ok_bind h₁
        obtain ⟨hx', rfl⟩ := ok_ofOption hx
        obtain ⟨rfl, rfl⟩ := ok_pure hp
        refine ⟨ls, _ :: a, rfl, hls, by simp [ha], fun st' => ?_⟩
        simp only [List.cons_append, XInstr.step]
        exact ok_bind_intro (ok_ofOption_intro hb' _) (ok_bind_intro (ok_ofOption_intro hx' _) rfl)
      · cases hty
  | .select, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨vc, _ | ⟨vb, _ | ⟨va, a⟩⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp at ha
      obtain ⟨rfl, rfl⟩ := ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · rename_i hc
        cases hty
        simp only [List.cons_append, XInstr.step] at h
        obtain ⟨c, s₁, hcv, hp⟩ := ok_bind h
        obtain ⟨hc', rfl⟩ := ok_ofOption hcv
        obtain ⟨rfl, rfl⟩ := ok_pure hp
        refine ⟨ls, _ :: a, rfl, hls, ?_, fun st' => ?_⟩
        · simp only [List.map_cons, ha]
          split <;> simp [hc.2]
        · simp only [List.cons_append, XInstr.step]
          exact ok_bind_intro (ok_ofOption_intro hc' _) rfl
      · cases hty
  | .memCopy, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨vn, _ | ⟨vs, _ | ⟨vd, a⟩⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp at ha
      obtain ⟨rfl, rfl⟩ := ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · cases hty
        simp only [List.cons_append, XInstr.step] at h
        obtain ⟨n, s₁, hn, h₁⟩ := ok_bind h
        obtain ⟨hn', rfl⟩ := ok_ofOption hn
        obtain ⟨sr, s₂, hsr, h₂⟩ := ok_bind h₁
        obtain ⟨hsr', rfl⟩ := ok_ofOption hsr
        obtain ⟨d, s₃, hd, h₃⟩ := ok_bind h₂
        obtain ⟨hd', rfl⟩ := ok_ofOption hd
        obtain ⟨bs, s₄, hl, h₄⟩ := ok_bind h₃
        obtain ⟨u, s₅, hs, hp⟩ := ok_bind h₄
        obtain ⟨rfl, rfl⟩ := ok_pure hp
        refine ⟨ls, a, rfl, hls, ha, fun st' => ?_⟩
        simp only [List.cons_append, XInstr.step]
        exact ok_bind_intro (ok_ofOption_intro hn' _) (ok_bind_intro (ok_ofOption_intro hsr' _)
          (ok_bind_intro (ok_ofOption_intro hd' _) (ok_bind_intro hl (ok_bind_intro hs rfl))))
      · cases hty
  | .ifElse res thn els, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨vc, a⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, ts⟩
      · simp at ha
      · simp only [List.map_cons, List.cons.injEq] at ha
        obtain ⟨rfl, ha⟩ := ha
        simp only [tyStep] at hty
        split at hty
        · rename_i hc
          cases hty
          obtain ⟨hct, hthn, hels⟩ := hc
          simp only [List.cons_append, XInstr.step] at h
          obtain ⟨c, s₁, hcv, h₁⟩ := ok_bind h
          obtain ⟨hc', rfl⟩ := ok_ofOption hcv
          by_cases h0 : c == 0
          · simp only [h0, ↓reduceIte] at h₁
            obtain ⟨ls', a', rfl, hls', ha', hall⟩ :=
              exec_frame hC els hels (a := []) (st := a ++ st) hls rfl (by simpa using h₁)
            refine ⟨ls', a' ++ a, by simp, hls', by simp [ha', ha], fun st' => ?_⟩
            simp only [List.cons_append, XInstr.step]
            refine ok_bind_intro (ok_ofOption_intro hc' _) ?_
            simp only [h0, ↓reduceIte]
            simpa using hall (a ++ st')
          · simp only [h0, ↓reduceIte, Bool.false_eq_true] at h₁
            obtain ⟨ls', a', rfl, hls', ha', hall⟩ :=
              exec_frame hC thn hthn (a := []) (st := a ++ st) hls rfl (by simpa using h₁)
            refine ⟨ls', a' ++ a, by simp, hls', by simp [ha', ha], fun st' => ?_⟩
            simp only [List.cons_append, XInstr.step]
            refine ok_bind_intro (ok_ofOption_intro hc' _) ?_
            simp only [h0, ↓reduceIte, Bool.false_eq_true]
            simpa using hall (a ++ st')
        · cases hty
  | .load t n sx off, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨va, a⟩
    · subst ha; cases t <;> simp [tyStep] at hty
    · rcases ts with _ | ⟨t₀, ts⟩
      · simp at ha
      · simp only [List.map_cons, List.cons.injEq] at ha
        obtain ⟨rfl, ha⟩ := ha
        rcases t with it | ft
        · simp only [tyStep] at hty
          split at hty
          · cases hty
            simp only [List.cons_append, XInstr.step] at h
            obtain ⟨x, s₁, hx, h₁⟩ := ok_bind h
            obtain ⟨hx', rfl⟩ := ok_ofOption hx
            obtain ⟨bs, s₂, hl, hp⟩ := ok_bind h₁
            obtain ⟨rfl, rfl⟩ := ok_pure hp
            refine ⟨ls, _ :: a, rfl, hls, by simp [ha, loadVal]; split <;> rfl, fun st' => ?_⟩
            simp only [List.cons_append, XInstr.step]
            exact ok_bind_intro (ok_ofOption_intro hx' _) (ok_bind_intro hl rfl)
          · cases hty
        · simp [tyStep] at hty
  | .store t n off, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    rcases a with _ | ⟨v, _ | ⟨va, a⟩⟩
    · subst ha; cases t <;> simp [tyStep] at hty
    · rcases ts with _ | ⟨t₁, _ | ⟨t₂, ts⟩⟩ <;> simp at ha
      subst ha; cases t <;> simp [tyStep] at hty
    · rcases ts with _ | ⟨t₁, _ | ⟨t₂, ts⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, ha⟩ := ha
      rcases t with it | ft
      · simp only [tyStep] at hty
        split at hty
        · cases hty
          simp only [List.cons_append, XInstr.step] at h
          obtain ⟨x, s₁, hx, h₁⟩ := ok_bind h
          obtain ⟨hx', rfl⟩ := ok_ofOption hx
          obtain ⟨u, s₂, hs, hp⟩ := ok_bind h₁
          obtain ⟨rfl, rfl⟩ := ok_pure hp
          refine ⟨ls, a, rfl, hls, ha, fun st' => ?_⟩
          simp only [List.cons_append, XInstr.step]
          exact ok_bind_intro (ok_ofOption_intro hx' _) (ok_bind_intro hs rfl)
        · cases hty
      · simp [tyStep] at hty

/-- **Framing, a sequence.** -/
theorem exec_frame (hC : CallsTyped M rt) : ∀ (is : List XInstr) {ts ts' : List NumType},
    tyExec rt lt is ts = some ts' →
    ∀ {ls a st : List Flat} {s s' : M.St} {f' : Silmaril.Wasm.Jco.Frame},
    ls.map (·.type) = lt → a.map (·.type) = ts →
    execX M is ⟨ls, a ++ st⟩ s (.ok f' s') → FrameOK M lt (execX M is) ls a st ts' s s' f'
  | [], ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    simp only [tyExec, Option.some.injEq] at hty
    subst hty
    have h' : (pure (⟨ls, a ++ st⟩ : Silmaril.Wasm.Jco.Frame) : RM M.St _) s (.ok f' s') := h
    obtain ⟨rfl, rfl⟩ := ok_pure h'
    exact ⟨ls, a, rfl, hls, ha, fun st' => rfl⟩
  | i :: is, ts, ts', hty, ls, a, st, s, s', f', hls, ha, h => by
    simp only [tyExec] at hty
    split at hty
    · rename_i ts₁ h₁
      rw [execX_cons] at h
      obtain ⟨f₁, s₁, hs₁, hr⟩ := ok_bind h
      obtain ⟨ls₁, a₁, rfl, hls₁, ha₁, hall₁⟩ := step_frame hC i h₁ hls ha hs₁
      obtain ⟨ls₂, a₂, rfl, hls₂, ha₂, hall₂⟩ := exec_frame hC is hty hls₁ ha₁ hr
      refine ⟨ls₂, a₂, rfl, hls₂, ha₂, fun st' => ?_⟩
      rw [execX_cons]
      exact ok_bind_intro (hall₁ st') (hall₂ st')
    · cases hty

end

end Silmaril.Proofs.Wasm.Jco.Real
