module

public import Silmaril.Sim.X86.G.Defs
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# The G simulator: globals, updates and the evaluation of method code

Lemmas about `gval`/`upd` under `Layout` and the evaluation of the generated code by
`Silmaril.Wasm.Logic.Core.exec1` (`exec1_gget`, `exec1_gset`, `exec1_c64`, `exec1_b64op`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1)

variable {H : Type} {s : Store H} {f : Frame}

theorem gval_eq (s : Store H) (f : Frame) (l : Loc) :
    gval s f l = (f.module.globals[l.idx]?).bind fun a => (s.globals[a]?).map (·.value) := by
  simp only [gval, Store.global?, Loc.gidx, Idx.toNat]
  cases f.module.globals[l.idx]? <;> simp [Option.bind]
  rename_i a
  cases s.globals[a]? <;> rfl

theorem Layout.upd_eq (h : Layout s f) (l : Loc) (v : Val) :
    ∃ a, f.module.globals[l.idx]? = some a ∧ a < s.globals.length ∧
      upd s f l v = s.setGlobal a v := by
  obtain ⟨a, ha, hlt⟩ := h.addr l
  exact ⟨a, ha, hlt, by simp [upd, ha]⟩

theorem Layout.upd (h : Layout s f) (l : Loc) (v : Val) : Layout (upd s f l v) f := by
  obtain ⟨a, -, -, he⟩ := h.upd_eq l v
  rw [he]
  exact ⟨fun l' => by
      obtain ⟨b, hb, hlt⟩ := h.addr l'
      exact ⟨b, hb, by simpa [Store.setGlobal] using hlt⟩,
    h.inj⟩

@[simp] theorem gval_upd (h : Layout s f) (l l' : Loc) (v : Val) :
    gval (upd s f l v) f l' = if l' = l then some v else gval s f l' := by
  obtain ⟨a, ha, hlt, he⟩ := h.upd_eq l v
  rw [he, gval_eq, gval_eq]
  obtain ⟨b, hb, -⟩ := h.addr l'
  rw [hb]
  simp only [Option.bind_some, Store.setGlobal, List.getElem?_modify]
  by_cases hl : l' = l
  · subst hl
    obtain rfl : b = a := by rw [ha] at hb; exact (Option.some.inj hb).symm
    simp [List.getElem?_eq_getElem hlt]
  · have hab : a ≠ b := fun e => hl (h.inj l' l a (e ▸ hb) ha)
    simp [hl, hab]

@[simp] theorem val_i64_inj {a b : BitVec 64} : Val.i64 a = Val.i64 b ↔ a = b := by
  constructor
  · intro h
    simp only [Val.i64, Val.num.injEq] at h
    cases h
    rfl
  · rintro rfl; rfl

/-! ## Evaluation of the generated instructions -/

theorem exec1_gget (s : Store H) (f : Frame) (rs : List Val) (l : Loc) :
    exec1 s f rs (gget l) = (gval s f l).map fun v => (s, f, v :: rs) := by
  simp only [exec1, gget, gval, Option.map_map]
  rfl

theorem exec1_gset (h : Layout s f) (rs : List Val) (l : Loc) (v : Val) :
    exec1 s f (v :: rs) (gset l) = some (upd s f l v, f, rs) := by
  obtain ⟨a, ha, hlt, he⟩ := h.upd_eq l v
  simp only [exec1, gset, Silmaril.Wasm.Logic.Core.popV, Option.bind_some, Store.global?, Loc.gidx,
    Idx.toNat]
  simp [ha, List.getElem?_eq_getElem hlt, he]

theorem exec1_c64 (s : Store H) (f : Frame) (rs : List Val) (c : BitVec 64) :
    exec1 s f rs (c64 c) = some (s, f, Val.i64 c :: rs) := rfl

theorem exec1_b64op (s : Store H) (f : Frame) (rs : List Val) (op : IntBinOp) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op op) =
      match intBinOp .i64 op x y with
      | .ok z => some (s, f, Val.i64 z :: rs)
      | .error _ => none := by
  cases h : intBinOp .i64 op x y <;>
    simp [exec1, b64op, Silmaril.Wasm.Logic.Core.popInt, Val.i64, h]

/-! Per operation, with the result typed at `BitVec 64` (the generic `intBinOp` result is typed
at `IntValue .i64`, which blocks `simp` matching on later instructions). -/

theorem exec1_add (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .add) = some (s, f, Val.i64 (x + y) :: rs) := by
  rw [exec1_b64op]; rfl
theorem exec1_sub (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .sub) = some (s, f, Val.i64 (x - y) :: rs) := by
  rw [exec1_b64op]; rfl
theorem exec1_and (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .and) = some (s, f, Val.i64 (x &&& y) :: rs) := by
  rw [exec1_b64op]; rfl
theorem exec1_or (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .or) = some (s, f, Val.i64 (x ||| y) :: rs) := by
  rw [exec1_b64op]; rfl
theorem exec1_xor (rs : List Val) (x y : BitVec 64) :
    exec1 s f (Val.i64 y :: Val.i64 x :: rs) (b64op .xor) = some (s, f, Val.i64 (x ^^^ y) :: rs) := by
  rw [exec1_b64op]; rfl
theorem exec1_shr63 (rs : List Val) (x : BitVec 64) :
    exec1 s f (Val.i64 63 :: Val.i64 x :: rs) (b64op (.shr .unsigned)) =
      some (s, f, Val.i64 (x >>> 63) :: rs) := by
  rw [exec1_b64op]; rfl

/-! ## The frame condition -/

theorem Frames.refl (s : Store H) (f : Frame) : Frames s s f := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frames.upd {s' : Store H} (h : Frames s s' f) (hl : Layout s' f) (l : Loc) (v : Val) :
    Frames s (upd s' f l v) f := by
  obtain ⟨a, ha, -, he⟩ := hl.upd_eq l v
  obtain ⟨hlen, hs, hg⟩ := h
  rw [he]
  refine ⟨by simp [Store.setGlobal, hlen], ?_, fun b hb => ?_⟩
  · rw [hs]; rfl
  · have hab : a ≠ b := fun e => hb l (e ▸ ha)
    simpa [Store.setGlobal, List.getElem?_modify, hab] using hg b hb

theorem Frames.trans {s₁ s₂ s₃ : Store H} (h₁ : Frames s₁ s₂ f) (h₂ : Frames s₂ s₃ f) :
    Frames s₁ s₃ f := by
  obtain ⟨l₁, e₁, g₁⟩ := h₁
  obtain ⟨l₂, e₂, g₂⟩ := h₂
  refine ⟨l₂.trans l₁, ?_, fun a ha => (g₂ a ha).trans (g₁ a ha)⟩
  rw [e₂, e₁]

end Silmaril.Sim.X86.G
