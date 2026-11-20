module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Defs
public import Silmaril.Semantics.Accept.Host.Thms

/-!
# Proofs: owned resource handles as typed AST payloads

* The table: `lookup_killAll_mem`, `lookup_killAll_not_mem`, `killAll_le`, `Le.refl`,
  `Le.trans`; resolution `resolve1_mono`, `resolveVals_mono`, `resolveOp_mono` (a table reached
  by moves resolves as the initial one, where it resolves); `resolve1_congr`,
  `resolveVals_congr`, `resolveOp_congr` (**resolution reads the table only at the moved
  handles**); `resolveOp_some`, `resolveOp_dead` (a move kills its handles), `resolveOp_of_dead`
  (a dead handle does not resolve).
* The host: `step_dead`, `run_dead` (a dead handle stays dead), `no_second_move`,
  `unresolved_step` (an unresolved write gives no handle a meaning); `wstep_write_congr`,
  `wstep_ctl`, `built_via`, `built_via_none`; `ownSim`, `ownLang_subset_via` (the stateless
  reading bounds the resource host without undefined writes); `run_congr`, `ownLang_congr`
  (dependence on the initial table only through the moved handles); `run_of_via`,
  `ownLang_eq_of_linear` (on traces moving no handle twice, the resource host is the stateless
  reading).
* Ownership: `run_append`, `run_takes`, `run_gives`, `linear_of_ob`.
* Borrows: `vals_isEmpty_of_borrow`, `witNode_borrow` (a payload vector with a `borrow` field
  has no value, so its call is no event).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
open Silmaril.Wasm.Resource (OEv obProto obStep owns held release Mode Protocol)

/-! ## The table -/

theorem lookup_killAll_mem {rt : RT} {hs : List (BitVec 32)} {h : BitVec 32} (r : Nat)
    (hh : h ∈ hs) : (rt.killAll hs).lookup r h = none := by
  unfold RT.lookup RT.killAll
  simp only [hh, ↓reduceIte]
  cases rt h <;> simp [ResEntry.kill]

theorem lookup_killAll_not_mem {rt : RT} {hs : List (BitVec 32)} {h : BitVec 32} (r : Nat)
    (hh : h ∉ hs) : (rt.killAll hs).lookup r h = rt.lookup r h := by
  unfold RT.lookup RT.killAll
  simp only [hh, ↓reduceIte]

theorem killAll_le (rt : RT) (hs : List (BitVec 32)) : (rt.killAll hs).Le rt := by
  intro r h rep hl
  by_cases hh : h ∈ hs
  · rw [lookup_killAll_mem r hh] at hl; cases hl
  · rwa [lookup_killAll_not_mem r hh] at hl

theorem Le.refl (rt : RT) : rt.Le rt := fun _ _ _ h => h

theorem Le.trans {a b c : RT} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c :=
  fun r h rep hl => h₂ r h rep (h₁ r h rep hl)

/-- The entry at `h` determines the lookups at `h`. -/
theorem lookup_congr {rt rt' : RT} {h : BitVec 32} (e : rt h = rt' h) (r : Nat) :
    rt.lookup r h = rt'.lookup r h := by
  unfold RT.lookup; rw [e]

theorem resolveVals_cons (rt : RT) (t : PTy) (ps : List PTy) (v : (ownRaw t).Val)
    (vs : PTy.Vals (ps.map ownRaw)) :
    resolveVals rt (t :: ps) (v, vs) =
      (resolve1 rt t v).bind fun a => (resolveVals rt ps vs).map fun as => (a, as) := rfl

theorem movedVals_cons (t : PTy) (ps : List PTy) (v : (ownRaw t).Val)
    (vs : PTy.Vals (ps.map ownRaw)) : movedVals (t :: ps) (v, vs) = moved1 t v ++ movedVals ps vs :=
  rfl

theorem resolve1_mono {rt rt₀ : RT} (hle : rt.Le rt₀) :
    ∀ {t : PTy} {v : (ownRaw t).Val} {a : t.Val}, resolve1 rt t v = some a →
      resolve1 rt₀ t v = some a
  | .own _, _, _, h => hle _ _ _ h
  | .bool, _, _, h | .s32, _, _, h | .u32, _, _, h | .s64, _, _, h | .u64, _, _, h
  | .string, _, _, h | .list _, _, _, h | .s8, _, _, h | .u8, _, _, h | .s16, _, _, h
  | .u16, _, _, h | .f32, _, _, h | .f64, _, _, h | .char, _, _, h | .fixedList _ _, _, _, h
  | .record _, _, _, h | .tuple _, _, _, h | .variant _, _, _, h | .enum _, _, _, h
  | .option _, _, _, h | .result _ _, _, _, h | .flags _, _, _, h | .borrow _, _, _, h => h

theorem resolveVals_mono {rt rt₀ : RT} (hle : rt.Le rt₀) :
    ∀ {ps : List PTy} {vs : PTy.Vals (ps.map ownRaw)} {a : PTy.Vals ps},
      resolveVals rt ps vs = some a → resolveVals rt₀ ps vs = some a
  | [], _, _, h => h
  | t :: ps, (v, vs), a, h => by
    rw [resolveVals_cons] at h ⊢
    rcases h1 : resolve1 rt t v with _ | x
    · rw [h1] at h; cases h
    rcases h2 : resolveVals rt ps vs with _ | y
    · rw [h1, h2] at h; cases h
    rw [h1, h2] at h
    rw [resolve1_mono hle h1, resolveVals_mono hle h2]
    exact h

theorem resolve1_congr {rt rt' : RT} :
    ∀ {t : PTy} {v : (ownRaw t).Val}, (∀ h ∈ moved1 t v, rt h = rt' h) →
      resolve1 rt t v = resolve1 rt' t v
  | .own r, v, h => lookup_congr (h _ (by simp [moved1])) r
  | .bool, _, _ | .s32, _, _ | .u32, _, _ | .s64, _, _ | .u64, _, _
  | .string, _, _ | .list _, _, _ | .s8, _, _ | .u8, _, _ | .s16, _, _
  | .u16, _, _ | .f32, _, _ | .f64, _, _ | .char, _, _ | .fixedList _ _, _, _
  | .record _, _, _ | .tuple _, _, _ | .variant _, _, _ | .enum _, _, _
  | .option _, _, _ | .result _ _, _, _ | .flags _, _, _ | .borrow _, _, _ => rfl

/-- **Resolution reads the table only at the moved handles.** -/
theorem resolveVals_congr {rt rt' : RT} :
    ∀ {ps : List PTy} {vs : PTy.Vals (ps.map ownRaw)}, (∀ h ∈ movedVals ps vs, rt h = rt' h) →
      resolveVals rt ps vs = resolveVals rt' ps vs
  | [], _, _ => rfl
  | t :: ps, (v, vs), h => by
    rw [movedVals_cons] at h
    rw [resolveVals_cons, resolveVals_cons, resolve1_congr fun x hx => h x (List.mem_append_left _ hx),
      resolveVals_congr fun x hx => h x (List.mem_append_right _ hx)]

/-- A resolved field names live handles. -/
theorem resolve1_live {rt : RT} :
    ∀ {t : PTy} {v : (ownRaw t).Val} {a : t.Val}, resolve1 rt t v = some a →
      ∀ h ∈ moved1 t v, ∃ r rep, rt.lookup r h = some rep
  | .own r, _, a, hv, h, hh => by
    simp only [moved1, List.mem_singleton] at hh
    subst hh
    exact ⟨r, a, hv⟩
  | .bool, _, _, _, _, hh | .s32, _, _, _, _, hh | .u32, _, _, _, _, hh
  | .s64, _, _, _, _, hh | .u64, _, _, _, _, hh | .string, _, _, _, _, hh
  | .list _, _, _, _, _, hh | .s8, _, _, _, _, hh | .u8, _, _, _, _, hh
  | .s16, _, _, _, _, hh | .u16, _, _, _, _, hh | .f32, _, _, _, _, hh
  | .f64, _, _, _, _, hh | .char, _, _, _, _, hh | .fixedList _ _, _, _, _, _, hh
  | .record _, _, _, _, _, hh | .tuple _, _, _, _, _, hh | .variant _, _, _, _, _, hh
  | .enum _, _, _, _, _, hh | .option _, _, _, _, _, hh | .result _ _, _, _, _, _, hh
  | .flags _, _, _, _, _, hh | .borrow _, _, _, _, _, hh => by simp [moved1] at hh

theorem resolveVals_live {rt : RT} :
    ∀ {ps : List PTy} {vs : PTy.Vals (ps.map ownRaw)} {a : PTy.Vals ps},
      resolveVals rt ps vs = some a → ∀ h ∈ movedVals ps vs, ∃ r rep, rt.lookup r h = some rep
  | [], _, _, _, _, hh => by simp [movedVals] at hh
  | t :: ps, (v, vs), a, hv, h, hh => by
    rw [movedVals_cons] at hh
    rw [resolveVals_cons] at hv
    rcases h1 : resolve1 rt t v with _ | x
    · rw [h1] at hv; cases hv
    rcases h2 : resolveVals rt ps vs with _ | y
    · rw [h1, h2] at hv; cases hv
    rcases List.mem_append.1 hh with hh | hh
    · exact resolve1_live h1 h hh
    · exact resolveVals_live h2 h hh

variable {S : WitSig}

theorem resolveOp_some {rt rt' : RT} {rop : ROp S} {op : Op S}
    (h : resolveOp S rt rop = some (op, rt')) :
    (movedOp S rop).Nodup ∧ rt' = rt.killAll (movedOp S rop) ∧
      ∃ a, resolveVals rt (S.params rop.1) rop.2 = some a ∧ op = ⟨rop.1, a⟩ := by
  unfold resolveOp at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨a, ha, rfl, rfl⟩ := h
    exact ⟨‹_ ∧ _›.2, rfl, a, ha, rfl⟩
  · cases h

/-- **Resolution reads the table only at the moved handles**, and the table after the move is
the table with them consumed. -/
theorem resolveOp_congr {rt rt' : RT} {rop : ROp S}
    (h : ∀ x ∈ movedOp S rop, rt x = rt' x) :
    resolveOp S rt' rop = (resolveOp S rt rop).map fun p => (p.1, rt'.killAll (movedOp S rop)) := by
  unfold resolveOp
  split
  · rw [resolveVals_congr (rt := rt) (rt' := rt') h]
    cases resolveVals rt' (S.params rop.1) rop.2 <;> rfl
  · rfl

theorem resolveOp_none_congr {rt rt' : RT} {rop : ROp S}
    (h : ∀ x ∈ movedOp S rop, rt x = rt' x) (hn : resolveOp S rt rop = none) :
    resolveOp S rt' rop = none := by
  rw [resolveOp_congr h, hn]; rfl

theorem resolveOp_mono {rt rt₀ rt' : RT} {rop : ROp S} {op : Op S} (hle : rt.Le rt₀)
    (h : resolveOp S rt rop = some (op, rt')) :
    resolveOp S rt₀ rop = some (op, rt₀.killAll (movedOp S rop)) := by
  obtain ⟨hnd, -, a, ha, rfl⟩ := resolveOp_some h
  have hadmitted : checkPTys .ownFields (S.params rop.1) = .ok () := by
    unfold resolveOp at h
    split at h
    · exact ‹_ ∧ _›.1
    · cases h
  unfold resolveOp
  simp only [hadmitted, hnd, and_self, ↓reduceIte, resolveVals_mono hle ha, Option.map_some]

/-- **A move consumes its handles.** -/
theorem resolveOp_dead {rt rt' : RT} {rop : ROp S} {op : Op S}
    (h : resolveOp S rt rop = some (op, rt')) : ∀ x ∈ movedOp S rop, rt'.Dead x := by
  obtain ⟨-, rfl, -⟩ := resolveOp_some h
  intro x hx r
  exact lookup_killAll_mem r hx

/-- **A dead handle does not resolve.** -/
theorem resolveOp_of_dead {rt : RT} {rop : ROp S} {x : BitVec 32} (hx : x ∈ movedOp S rop)
    (hd : rt.Dead x) : resolveOp S rt rop = none := by
  unfold resolveOp
  split
  · rcases hv : resolveVals rt (S.params rop.1) rop.2 with _ | a
    · rfl
    · obtain ⟨r, rep, hl⟩ := resolveVals_live hv x hx
      rw [hd r] at hl
      cases hl
  · rfl

/-! ## The host -/

variable {X : Type} {W : Writer (Op S) X} {pol : Policy (BitVec 32)}

/-- **A dead handle stays dead** along a step. -/
theorem step_dead {s s' : OwnState X} {e : WEv (ROp S) (BitVec 32)} {A : Set X}
    (hs : OwnStep W pol s e s' A) {x : BitVec 32} (hd : s.rt.Dead x) : s'.rt.Dead x := by
  cases hs with
  | @move _ _ _ _ rop _ _ _ _ hr _ =>
    obtain ⟨-, rfl, -⟩ := resolveOp_some hr
    intro r
    by_cases hx : x ∈ movedOp S rop
    · exact lookup_killAll_mem r hx
    · rw [lookup_killAll_not_mem r hx]; exact hd r
  | badFail => exact hd
  | badChaos => exact hd
  | chaos => exact hd
  | other => exact hd

/-- **A dead handle stays dead** along a run. -/
theorem run_dead {rt₀ : RT} {s s' : OwnState X} {es : List (WEv (ROp S) (BitVec 32))} {A : Set X}
    (hr : (ownHost W pol rt₀).Run s es s' A) {x : BitVec 32} (hd : s.rt.Dead x) : s'.rt.Dead x := by
  induction hr with
  | nil => exact hd
  | cons hs _ ih => exact ih (step_dead hs hd)

/-- **A consumed handle is never consumed again**: after a write moves `x`, a later write moving
`x` does not resolve, at any point of any continuation. -/
theorem no_second_move {rt₀ : RT} {s₁ s₂ s₃ : OwnState X} {rop rop' : ROp S} {op : Op S}
    {es : List (WEv (ROp S) (BitVec 32))} {B : Set X} {x : BitVec 32}
    (hm : resolveOp S s₁.rt rop = some (op, s₂.rt)) (hx : x ∈ movedOp S rop)
    (hr : (ownHost W pol rt₀).Run s₂ es s₃ B) (hx' : x ∈ movedOp S rop') :
    resolveOp S s₃.rt rop' = none :=
  resolveOp_of_dead hx' (run_dead hr (resolveOp_dead hm x hx))

/-- **An unresolved write gives no handle a meaning**: the store is unchanged, and nothing is
accepted unless the policy makes invalid writes undefined. -/
theorem unresolved_step {s s' : OwnState X} {rop : ROp S} {args : List (BitVec 32)}
    {r : BitVec 32} {A : Set X} (hs : OwnStep W pol s (.write rop args r) s' A)
    (hl : s.w.phase = .live) (hn : resolveOp S s.rt rop = none) :
    s'.w.store = s.w.store ∧ (A = ∅ ∨ pol.onWrite = .ub) := by
  cases hs with
  | move hr _ => rw [hn] at hr; cases hr
  | badFail => exact ⟨rfl, .inl rfl⟩
  | badChaos _ _ hu => exact ⟨rfl, .inr hu⟩
  | chaos hc => rw [hl] at hc; cases hc
  | other he => cases he

/-! ## Steps that accept nothing -/

/-- An export-call boundary in `live` changes nothing. -/
theorem step_enter {s s' : OwnState X} {A : Set X} (hs : OwnStep W pol s .enter s' A)
    (hl : s.w.phase = .live) : s' = s ∧ A = ∅ := by
  obtain ⟨rt, σ, B, ph⟩ := s
  simp only at hl
  subst hl
  cases hs with
  | chaos hc => cases hc
  | other he hw' =>
    simp only [WEv.ctl, Option.some.injEq] at he
    subst he
    cases hw'
    exact ⟨rfl, rfl⟩

/-- **A write in `live` accepts nothing and changes the store at most at its answer** (no
undefined writes); the table is consumed exactly when the write resolves. -/
theorem step_write {s s' : OwnState X} {rop : ROp S} {args : List (BitVec 32)} {r : BitVec 32}
    {A : Set X} (hs : OwnStep W pol s (.write rop args r) s' A) (hl : s.w.phase = .live)
    (hw : pol.onWrite ≠ .ub) :
    A = ∅ ∧ s'.w.phase = .live ∧ (∀ x, x ≠ r → s'.w.store x = s.w.store x) ∧
      ((∃ op, resolveOp S s.rt rop = some (op, s'.rt)) ∨
        (resolveOp S s.rt rop = none ∧ s'.rt = s.rt)) := by
  obtain ⟨rt, σ, B, ph⟩ := s
  simp only at hl
  subst hl
  cases hs with
  | move hr hw' =>
    cases hw' with
    | writeOk _ _ _ =>
      exact ⟨rfl, rfl, fun x hx => Function.update_of_ne hx _ _, .inl ⟨_, hr⟩⟩
    | writeFail _ _ => exact ⟨rfl, rfl, fun _ _ => rfl, .inl ⟨_, hr⟩⟩
    | writeChaos _ hu _ => exact absurd hu hw
    | writeFixed _ _ h => cases h
  | badFail hn _ _ _ => exact ⟨rfl, rfl, fun _ _ => rfl, .inr ⟨hn, rfl⟩⟩
  | badChaos _ _ hu => exact absurd hu hw
  | chaos hc => cases hc
  | other he => cases he

/-- **An invalid accept accepts nothing** (no undefined accepts). -/
theorem step_accept_none {s s' : OwnState X} {h : BitVec 32} {A : Set X}
    (hs : OwnStep W pol s (.accept h) s' A) (hl : s.w.phase = .live) (hn : s.w.store h = none)
    (ha : pol.onAccept ≠ .ub) : A = ∅ := by
  obtain ⟨rt, σ, B, ph⟩ := s
  simp only at hl hn
  subst hl
  cases hs with
  | chaos hc => cases hc
  | other he hw' =>
    simp only [WEv.ctl, Option.some.injEq] at he
    subst he
    cases hw' with
    | acceptOk ht => rw [hn] at ht; cases ht
    | acceptCallTrap => rfl
    | acceptSessionTrap => rfl
    | acceptIgnore => rfl
    | acceptChaos _ hu => exact absurd hu ha
    | acceptFixed _ _ h => cases h

/-- **Moving a handle twice yields no second tree**: from a `live` state in which `r₂` denotes
nothing, the trace `enter, write rop _ r₁, write rop _ r₂, accept r₂` (the same raw operation,
moving a handle `x`, twice) accepts nothing, for every policy without undefined behaviour. -/
theorem run_twice {rt₀ : RT} {s s' : OwnState X} {rop : ROp S} {args₁ args₂ : List (BitVec 32)}
    {r₁ r₂ : BitVec 32} {A : Set X} {x : BitVec 32} (hx : x ∈ movedOp S rop)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) (hl : s.w.phase = .live)
    (hn : s.w.store r₂ = none) (hr : r₂ ≠ r₁)
    (hrun : (ownHost W pol rt₀).Run s
      [.enter, .write rop args₁ r₁, .write rop args₂ r₂, .accept r₂] s' A) : A = ∅ := by
  cases hrun with
  | @cons _ s₁ _ _ _ A₁ _ h₁ hrun =>
  cases hrun with
  | @cons _ s₂ _ _ _ A₂ _ h₂ hrun =>
  cases hrun with
  | @cons _ s₃ _ _ _ A₃ _ h₃ hrun =>
  cases hrun with
  | @cons _ s₄ _ _ _ A₄ _ h₄ hrun =>
  cases hrun with
  | nil =>
  obtain ⟨rfl, rfl⟩ := step_enter h₁ hl
  obtain ⟨rfl, hl₂, hst₂, hrt₂⟩ := step_write h₂ hl hw
  have hn₃ : resolveOp S s₂.rt rop = none := by
    rcases hrt₂ with ⟨op, hm⟩ | ⟨hn', hrt⟩
    · exact resolveOp_of_dead hx (resolveOp_dead hm x hx)
    · rw [hrt]; exact hn'
  obtain ⟨hst₃, -⟩ := unresolved_step h₃ hl₂ hn₃
  obtain ⟨rfl, hl₃, -, -⟩ := step_write h₃ hl₂ hw
  have h₄' := step_accept_none h₄ hl₃ (by rw [hst₃, hst₂ _ hr]; exact hn) ha
  subst h₄'
  simp

/-! ## Writer steps across operation types -/

theorem wstep_write_congr {Op₁ Op₂ : Type} {W₁ : Writer Op₁ X} {W₂ : Writer Op₂ X}
    {op₁ : Op₁} {op₂ : Op₂} {args : List (BitVec 32)} {r : BitVec 32}
    {w w' : WState (BitVec 32) X} {A : Set X}
    (hb : ∀ σ, W₁.built σ op₁ args = W₂.built σ op₂ args)
    (h : WStep W₁ pol none w (.write op₁ args r) w' A) :
    WStep W₂ pol none w (.write op₂ args r) w' A := by
  cases h with
  | writeOk h₁ h₂ h₃ => exact .writeOk ((hb _).symm.trans h₁) h₂ h₃
  | writeFail h₁ h₂ => exact .writeFail h₁ (by rwa [← hb])
  | writeChaos h₁ h₂ h₃ => exact .writeChaos ((hb _).symm.trans h₁) h₂ h₃
  | writeFixed _ _ h => cases h
  | chaos => exact .chaos _

theorem ctl_symm {Op₁ Op₂ : Type} {e : WEv Op₁ (BitVec 32)} {e' : WEv Op₂ (BitVec 32)}
    (h : WEv.ctl e = some e') : WEv.ctl e' = some e := by
  cases e <;> simp only [WEv.ctl, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem ctl_write {Op₁ Op₂ : Type} {e : WEv Op₁ (BitVec 32)} :
    (∀ op args r, e ≠ .write op args r) → ∃ e' : WEv Op₂ (BitVec 32), WEv.ctl e = some e' := by
  intro h
  cases e with
  | write op args r => exact absurd rfl (h op args r)
  | _ => exact ⟨_, rfl⟩

theorem wstep_ctl {Op₁ Op₂ : Type} {W₁ : Writer Op₁ X} {W₂ : Writer Op₂ X}
    {e : WEv Op₁ (BitVec 32)} {e' : WEv Op₂ (BitVec 32)} {w w' : WState (BitVec 32) X}
    {A : Set X} (he : WEv.ctl e = some e') (h : WStep W₁ pol none w e w' A) :
    WStep W₂ pol none w e' w' A := by
  cases e <;> simp only [WEv.ctl, Option.some.injEq, reduceCtorEq] at he <;> subst he <;>
    cases h
  all_goals first
    | exact .acceptOk ‹_› | exact .acceptCallTrap ‹_› ‹_› | exact .acceptSessionTrap ‹_› ‹_›
    | exact .acceptIgnore ‹_› ‹_› | exact .acceptChaos ‹_› ‹_› ‹_›
    | exact .acceptErrOk ‹_› | exact .acceptErrBad ‹_› | exact .acceptAll
    | exact .acceptBatch _ | exact .enter | exact .resume | exact .chaos _
    | simp_all

theorem built_via {rt₀ x : RT} {rop : ROp S} {op : Op S}
    (h : resolveOp S rt₀ rop = some (op, x)) (σ : Env (BitVec 32) X) (args : List (BitVec 32)) :
    (viaRT W rt₀).built σ rop args = W.built σ op args := by
  simp only [Writer.built, viaRT, h, Option.bind_some]

theorem built_via_none {rt₀ : RT} {rop : ROp S} (h : resolveOp S rt₀ rop = none)
    (σ : Env (BitVec 32) X) (args : List (BitVec 32)) :
    (viaRT W rt₀).built σ rop args = none := by
  simp only [Writer.built, viaRT, h, Option.bind_none]
  cases σ.lookupAll args <;> rfl

/-! ## The stateless reading bounds the resource host -/

/-- **The resource host is simulated by the stateless reading** in the initial table, for
policies without undefined writes: the current table is reached from `rt₀` by moves. -/
theorem ownSim (rt₀ : RT) (hw : pol.onWrite ≠ .ub) :
    Host.Sim (ownHost W pol rt₀) (writer (viaRT W rt₀) pol) id
      (fun s w => s.w = w ∧ s.rt.Le rt₀) where
  init := ⟨rfl, Le.refl _⟩
  step := by
    rintro s _ e s' A ⟨rfl, hle⟩ hs
    cases hs with
    | move hr hw' =>
      obtain ⟨-, rfl, -⟩ := resolveOp_some hr
      exact ⟨_, _, wstep_write_congr (fun σ => (built_via (resolveOp_mono hle hr) σ _).symm) hw',
        ⟨rfl, Le.trans (killAll_le _ _) hle⟩, le_rfl⟩
    | @badFail rt w rop args r _ hl hf hs =>
      obtain ⟨σ, B, ph⟩ := w
      simp only at hl
      subst hl
      exact ⟨_, _, .writeFail hs (.inr hf), ⟨rfl, hle⟩, le_rfl⟩
    | badChaos _ _ hu => exact absurd hu hw
    | @chaos rt w e hc =>
      obtain ⟨σ, B, ph⟩ := w
      simp only at hc
      subst hc
      exact ⟨_, _, .chaos _, ⟨rfl, hle⟩, le_rfl⟩
    | other he hw' => exact ⟨_, _, wstep_ctl (ctl_symm he) hw', ⟨rfl, hle⟩, le_rfl⟩

/-- **The stateless reading bounds the resource host** (no undefined writes). -/
theorem ownLang_subset_via (rt₀ : RT) (hw : pol.onWrite ≠ .ub)
    (T : Set (List (WEv (ROp S) (BitVec 32)))) :
    ownLang W pol rt₀ T ⊆ writerLang (viaRT W rt₀) pol T :=
  Host.lang_subset_of_sim_id (ownSim rt₀ hw) T

/-! ## Dependence on the initial table -/

theorem tmoved_ctl {Op₂ : Type} {e : WEv (ROp S) (BitVec 32)} {e' : WEv Op₂ (BitVec 32)}
    (he : WEv.ctl e = some e') (es : List (WEv (ROp S) (BitVec 32))) :
    tmoved S (e :: es) = tmoved S es := by
  cases e <;> simp only [WEv.ctl, reduceCtorEq] at he <;> rfl

theorem killAll_congr {rt rt' : RT} {hs : List (BitVec 32)} {x : BitVec 32}
    (h : rt x = rt' x) : rt.killAll hs x = rt'.killAll hs x := by
  unfold RT.killAll; rw [h]

/-- **Runs depend on the table only at the handles they move.** -/
theorem run_congr {rt₀ rt₀' : RT} :
    ∀ {es : List (WEv (ROp S) (BitVec 32))} {rt₁ rt₂ : RT} {w : WState (BitVec 32) X}
      {s : OwnState X} {A : Set X},
      (ownHost W pol rt₀).Run ⟨rt₁, w⟩ es s A → (∀ x ∈ tmoved S es, rt₁ x = rt₂ x) →
      ∃ rt₂', (ownHost W pol rt₀').Run ⟨rt₂, w⟩ es ⟨rt₂', s.w⟩ A
  | [], _, rt₂, _, _, _, hr, _ => by
    cases hr
    exact ⟨rt₂, .nil _⟩
  | e :: es, rt₁, rt₂, w, s, A, hr, hag => by
    cases hr with
    | cons hs hrest =>
      cases hs with
      | @move _ _ _ _ rop _ _ _ _ hrs hw' =>
        have hm : ∀ x ∈ movedOp S rop, rt₁ x = rt₂ x :=
          fun x hx => hag x (List.mem_append_left _ hx)
        obtain ⟨-, rfl, -⟩ := resolveOp_some hrs
        have h₂ := resolveOp_congr hm
        rw [hrs] at h₂
        obtain ⟨rt₃, hr₃⟩ := run_congr (rt₂ := rt₂.killAll (movedOp S rop)) hrest
          fun x hx => killAll_congr (hag x (List.mem_append_right _ hx))
        exact ⟨rt₃, .cons (.move h₂ hw') hr₃⟩
      | @badFail _ _ rop _ _ hn hl hf hs' =>
        obtain ⟨rt₃, hr₃⟩ := run_congr hrest fun x hx => hag x (List.mem_append_right _ hx)
        exact ⟨rt₃, .cons (.badFail (resolveOp_none_congr
          (fun x hx => hag x (List.mem_append_left _ hx)) hn) hl hf hs') hr₃⟩
      | @badChaos _ _ rop _ _ hn hl hu =>
        obtain ⟨rt₃, hr₃⟩ := run_congr hrest fun x hx => hag x (List.mem_append_right _ hx)
        exact ⟨rt₃, .cons (.badChaos (resolveOp_none_congr
          (fun x hx => hag x (List.mem_append_left _ hx)) hn) hl hu) hr₃⟩
      | chaos hc =>
        have hag' : ∀ x ∈ tmoved S es, rt₁ x = rt₂ x := fun x hx => hag x (by
          cases e <;> simp only [tmoved, List.mem_append] <;> first | exact hx | exact .inr hx)
        obtain ⟨rt₃, hr₃⟩ := run_congr hrest hag'
        exact ⟨rt₃, .cons (.chaos hc) hr₃⟩
      | other he hw' =>
        rw [tmoved_ctl he] at hag
        obtain ⟨rt₃, hr₃⟩ := run_congr hrest hag
        exact ⟨rt₃, .cons (.other he hw') hr₃⟩

/-- **The language depends on the initial table only at the moved handles.** -/
theorem ownLang_congr {rt₀ rt₀' : RT} {T : Set (List (WEv (ROp S) (BitVec 32)))}
    (h : ∀ t ∈ T, ∀ x ∈ tmoved S t, rt₀ x = rt₀' x) :
    ownLang W pol rt₀ T = ownLang W pol rt₀' T := by
  ext y
  simp only [ownLang, Host.mem_lang]
  constructor
  · rintro ⟨t, ht, s, A, hr, hy⟩
    obtain ⟨rt₂, hr₂⟩ := run_congr (rt₀' := rt₀') hr (h t ht)
    exact ⟨t, ht, _, A, hr₂, hy⟩
  · rintro ⟨t, ht, s, A, hr, hy⟩
    obtain ⟨rt₂, hr₂⟩ := run_congr (rt₀' := rt₀) hr fun x hx => (h t ht x hx).symm
    exact ⟨t, ht, _, A, hr₂, hy⟩

/-! ## Linear traces -/

/-- **On a trace moving no handle twice, a run of the stateless reading is a run of the resource
host.** -/
theorem run_of_via {rt₀ : RT} :
    ∀ {es : List (WEv (ROp S) (BitVec 32))} {rt : RT} {w w' : WState (BitVec 32) X} {A : Set X},
      (writer (viaRT W rt₀) pol).Run w es w' A → (tmoved S es).Nodup →
      (∀ x ∈ tmoved S es, rt x = rt₀ x) →
      ∃ rt', (ownHost W pol rt₀).Run ⟨rt, w⟩ es ⟨rt', w'⟩ A
  | [], rt, _, _, _, hr, _, _ => by
    cases hr
    exact ⟨rt, .nil _⟩
  | e :: es, rt, w, w', A, hr, hnd, hag => by
    cases hr with
    | cons hs hrest =>
      by_cases hwr : ∃ rop args r, e = WEv.write rop args r
      · obtain ⟨rop, args, r, rfl⟩ := hwr
        simp only [tmoved] at hnd hag
        have hm : ∀ x ∈ movedOp S rop, rt₀ x = rt x :=
          fun x hx => (hag x (List.mem_append_left _ hx)).symm
        have hdisj := (List.nodup_append.1 hnd).2.2
        rcases hres : resolveOp S rt₀ rop with _ | ⟨op, x₀⟩
        · have hn : resolveOp S rt rop = none := resolveOp_none_congr hm hres
          obtain ⟨rt', hr'⟩ := run_of_via hrest (List.nodup_append.1 hnd).2.1
            fun x hx => hag x (List.mem_append_right _ hx)
          cases hs with
          | writeOk hb _ _ => rw [built_via_none hres] at hb; cases hb
          | writeFail hsn hf =>
            rw [built_via_none hres] at hf
            simp only [Option.isSome_none, Bool.false_eq_true, false_or] at hf
            exact ⟨rt', .cons (.badFail hn rfl hf hsn) hr'⟩
          | writeChaos _ hu _ => exact ⟨rt', .cons (.badChaos hn rfl hu) hr'⟩
          | writeFixed _ _ h => cases h
          | chaos => exact ⟨rt', .cons (.chaos rfl) hr'⟩
        · have h₂ := resolveOp_congr hm
          rw [hres] at h₂
          obtain ⟨rt', hr'⟩ := run_of_via hrest (List.nodup_append.1 hnd).2.1
            (rt := rt.killAll (movedOp S rop)) fun x hx => by
              have hx' : x ∉ movedOp S rop := fun hmx => hdisj x hmx x hx rfl
              unfold RT.killAll
              simp only [hx', ↓reduceIte]
              exact hag x (List.mem_append_right _ hx)
          exact ⟨rt', .cons (.move h₂
            (wstep_write_congr (fun σ => built_via hres σ args) hs)) hr'⟩
      · obtain ⟨e', he⟩ := ctl_write (Op₂ := Op S) (fun op args r h => hwr ⟨op, args, r, h⟩)
        rw [tmoved_ctl he] at hnd hag
        obtain ⟨rt', hr'⟩ := run_of_via hrest hnd hag
        exact ⟨rt', .cons (.other he (wstep_ctl he hs)) hr'⟩

/-- **On traces moving no handle twice the resource host is the stateless reading** in the
initial table (no undefined writes). -/
theorem ownLang_eq_of_linear (rt₀ : RT) (hw : pol.onWrite ≠ .ub)
    {T : Set (List (WEv (ROp S) (BitVec 32)))} (hT : ∀ t ∈ T, (tmoved S t).Nodup) :
    ownLang W pol rt₀ T = writerLang (viaRT W rt₀) pol T := by
  refine Set.Subset.antisymm (ownLang_subset_via rt₀ hw T) ?_
  intro y hy
  simp only [writerLang, Host.mem_lang] at hy
  obtain ⟨t, ht, w, A, hr, hyA⟩ := hy
  obtain ⟨rt', hr'⟩ := run_of_via (rt := rt₀) hr (hT t ht) fun _ _ => rfl
  simp only [ownLang, Host.mem_lang]
  exact ⟨t, ht, _, A, hr', hyA⟩

/-! ## The ownership protocol -/

theorem run_append {St E : Type} (p : Protocol St E) (q : St) (a b : List E) :
    p.run q (a ++ b) = (p.run q a).bind fun q' => p.run q' b := by
  induction a generalizing q with
  | nil => rfl
  | cons e a ih =>
    simp only [List.cons_append, Protocol.run]
    cases p.step q e with
    | none => rfl
    | some q' => exact ih q'

theorem held_iff {L : List (BitVec 32 × Mode)} {h : BitVec 32} :
    held L h = true ↔ ∃ m, (h, m) ∈ L := by
  simp [held, List.any_eq_true]

theorem run_takes : ∀ (hs : List (BitVec 32)) (L : List (BitVec 32 × Mode)),
    hs.Nodup → (∀ h ∈ hs, held L h = false) →
    (obProto (BitVec 32)).run (some L) (hs.map OEv.take) =
      some (some (hs.reverse.map (fun h => (h, Mode.owned)) ++ L))
  | [], L, _, _ => rfl
  | h :: hs, L, hnd, hfree => by
    have hh : held L h = false := hfree h (List.mem_cons_self ..)
    simp only [List.map_cons, Protocol.run, obProto, obStep, hh, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some]
    have := run_takes hs ((h, .owned) :: L) (List.nodup_cons.1 hnd).2 fun g hg => by
      rcases hgl : held ((h, .owned) :: L) g with _ | _
      · rfl
      · obtain ⟨m, hm⟩ := held_iff.1 hgl
        rcases List.mem_cons.1 hm with hm | hm
        · cases hm; exact absurd hg (List.nodup_cons.1 hnd).1
        · have := hfree g (List.mem_cons_of_mem _ hg)
          rw [show held L g = true from held_iff.2 ⟨m, hm⟩] at this
          cases this
    simpa [obProto, List.reverse_cons, List.map_append] using this

theorem owns_release_self (L : List (BitVec 32 × Mode)) (h : BitVec 32) :
    owns (release L h) h = false := by
  simp [owns, release, List.mem_filter]

theorem owns_of_release {L : List (BitVec 32 × Mode)} {h g : BitVec 32}
    (hg : owns (release L h) g = true) : owns L g = true := by
  simp only [owns, release, List.contains_iff_mem, List.mem_filter] at hg ⊢
  exact hg.1

theorem run_gives : ∀ (gs : List (BitVec 32)) (L : List (BitVec 32 × Mode)) q,
    (obProto (BitVec 32)).run (some L) (gs.map OEv.give) = some q →
      gs.Nodup ∧ ∀ g ∈ gs, owns L g = true
  | [], _, _, _ => ⟨List.nodup_nil, by simp⟩
  | g :: gs, L, q, h => by
    simp only [List.map_cons, Protocol.run, obProto, obStep] at h
    split at h
    · rename_i ho
      simp only [Option.bind_some] at h
      obtain ⟨hnd, hall⟩ := run_gives gs (release L g) q h
      refine ⟨List.nodup_cons.2 ⟨fun hg => ?_, hnd⟩, ?_⟩
      · have := hall g hg
        rw [owns_release_self] at this
        cases this
      · intro g' hg'
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact ho
        · exact owns_of_release (hall g' hg')
    · cases h

/-- **A trace accepted by the ownership protocol moves no handle twice**, and moves only handles
the module owned initially. -/
theorem linear_of_ob {L₀ : List (BitVec 32)} {es : List (WEv (ROp S) (BitVec 32))}
    (hL : L₀.Nodup) (h : (obProto (BitVec 32)).Accepts (L₀.map OEv.take ++ ownGives S es)) :
    (tmoved S es).Nodup ∧ ∀ x ∈ tmoved S es, x ∈ L₀ := by
  unfold Protocol.Accepts at h
  rw [run_append, show (obProto (BitVec 32)).init = some [] from rfl,
    run_takes L₀ [] hL (fun _ _ => rfl), List.append_nil, Option.bind_some] at h
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨hnd, hall⟩ := run_gives _ _ q hq
  refine ⟨hnd, fun x hx => ?_⟩
  have := hall x hx
  simp only [owns, List.contains_iff_mem, List.mem_map, List.mem_reverse, Prod.mk.injEq,
    and_true] at this
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

/-! ## Borrows -/

theorem vals_isEmpty_of_borrow : ∀ {ps : List PTy} {r : Nat}, PTy.borrow r ∈ ps →
    IsEmpty (PTy.Vals ps)
  | t :: ps, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨fun v => (v : Empty × PTy.Vals ps).1.elim⟩
    · have := vals_isEmpty_of_borrow h
      exact ⟨fun v => this.false (v : t.Val × PTy.Vals ps).2⟩

/-- **A `borrow` payload field is never decoded**: a call naming a tag with one is no event. -/
theorem witNode_borrow {S : WitSig} {tagOf : BitVec 32 → Option S.Tag}
    {o : Silmaril.Wasm.Game.Accept.Callout} {op : Op S} {hs : List (BitVec 32)}
    (_ : Callout.witNode S tagOf o = some (op, hs)) (r : Nat) : PTy.borrow r ∉ S.params op.1 :=
  fun hb => (vals_isEmpty_of_borrow hb).false op.2

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn
