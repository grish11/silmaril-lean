module

public import Silmaril.Proofs.Sim.X86Real.Common
public import Silmaril.Wasm.Logic.VCCalls.Thms

/-!
# Representation G: the five accessors of `simG` meet their contracts
A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC

set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H}

set_option hygiene false in
/-- `rsetG_total` at the register `k` (one theorem per register, elaborated in parallel). -/
local macro "rsetG_case" name:ident k:num : command => `(
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem $name {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hrs : rs.length = 0) (s : Store H)
    (hok : okG mi s) (v : BitVec 64) :
    wpc (fun _ _ _ _ => True) 0 (fn simG 1).body
      (fnPost rs.length ((rsetSpec (repG mi) fi a).post s [Val.i32 (BitVec.ofNat 32 $k), Val.i64 v]))
      s (Frame.forCall mi [Val.i32 (BitVec.ofNat 32 $k), Val.i64 v] (fn simG 1).locals) [] := by
  have hl : (BitVec.ofNat 32 $k).toNat < 17 := by decide
  obtain ⟨a', g, h1, h2, h3⟩ := getG hok hl
  have hset := setG hok (by omega) h1 (by simp [h2]) (Val.i64 v) (.inl ⟨hl, v, rfl⟩)
  have hk' : (BitVec.ofNat 32 $k).toNat = $k := by decide
  rw [hk'] at h1 hset
  simp only [valNum_i64, valNum_i32] at hset
  simp only [Val.i64, Val.i32] at hset
  simp [↓tableVC_cons_self, ↓tableVC_cons_of_ne, ↓tableVC_nil_of_le,
    h1, h2, h3, hset, hrs, fn, simG, wpc, ctl, enterVC, labelQ_normal, labelQ_br_zero, labelQ_br_succ, labelQ_ret, labelQ_trap, labelQ_throw, labelQ_tail, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat, Val.i32, Val.i64, Store.global?,
    Silmaril.Wasm.Logic.Core.popV, rsetSpec, repG])

/-! ## Reading the G representation -/

theorem getG {mi : ModuleInst} {s : Store H} {j : Nat} (hok : okG mi s) (hj : j < 17) :
    ∃ a g, mi.globals[j]? = some a ∧ s.globals[a]? = some g ∧
      g.value = Val.i64 (gv s mi j) := by
  unfold okG at hok
  obtain ⟨-, hr, -⟩ := hok
  obtain ⟨a, g, v, h1, h2, h3⟩ := hr j hj
  refine ⟨a, g, h1, h2, ?_⟩
  have : gv s mi j = v := by simp only [gv, h1, h2, h3]; rfl
  rw [this, h3]

theorem getGf {mi : ModuleInst} {s : Store H} {j : Nat} (hok : okG mi s) (h1 : 17 ≤ j)
    (h2 : j < 24) : ∃ a g, mi.globals[j]? = some a ∧ s.globals[a]? = some g ∧
      g.value = Val.i32 ((gv s mi j).setWidth 32) ∧ (gv s mi j).toNat < 2 := by
  unfold okG at hok
  obtain ⟨-, -, hf⟩ := hok
  obtain ⟨a, g, v, h1, h2, h3, h4⟩ := hf j h1 h2
  have : gv s mi j = v.setWidth 64 := by simp only [gv, h1, h2, h3]; rfl
  refine ⟨a, g, h1, h2, ?_, ?_⟩
  · rw [h3, this]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; have := v.isLt; omega
  · rw [this]; simp; omega

/-! ## Writing the G representation -/

theorem globals_setGlobal (s : Store H) (a : Nat) (v : Val) (k : Nat) :
    (s.setGlobal a v).globals[k]? =
      if a = k then (s.globals[k]?).map (fun g => { g with value := v }) else s.globals[k]? := by
  simp only [Store.setGlobal, List.getElem?_modify]
  split <;> simp_all

@[simp] theorem valNum_i64 (v : BitVec 64) : valNum (Val.i64 v) = v := rfl
@[simp] theorem valNum_i32 (v : BitVec 32) : valNum (Val.i32 v) = v.setWidth 64 := rfl

theorem gv_set {mi : ModuleInst} {s : Store H} {l a : Nat} (hok : okG mi s) (hl : l < 24)
    (ha : mi.globals[l]? = some a) (hs : (s.globals[a]?).isSome) (v : Val) :
    gv (s.setGlobal a v) mi = updL (gv s mi) l (valNum v) := by
  funext k
  unfold updL
  by_cases hk : k = l
  · subst hk
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hs
    simp [gv, ha, globals_setGlobal, hg]
  · simp only [hk, ite_false, gv]
    cases hb : mi.globals[k]? with
    | none => rfl
    | some b =>
      have hab : a ≠ b := fun h => hk (hok.1 l k a hl ha (h ▸ hb)).symm
      simp [globals_setGlobal, hab]

theorem okG_set {mi : ModuleInst} {s : Store H} {l a : Nat} (hok : okG mi s) (hl : l < 24)
    (ha : mi.globals[l]? = some a) (v : Val)
    (hv : (l < 17 ∧ ∃ w, v = Val.i64 w) ∨ (17 ≤ l ∧ ∃ w : BitVec 32, v = Val.i32 w ∧ w.toNat < 2)) :
    okG mi (s.setGlobal a v) := by
  obtain ⟨hinj, hr, hf⟩ : okG mi s := hok
  have hab : ∀ k b, k ≠ l → mi.globals[k]? = some b → a ≠ b :=
    fun k b hkl hb h => hkl (hinj l k a hl ha (h ▸ hb)).symm
  have hba : ∀ k b, k = l → mi.globals[k]? = some b → a = b :=
    fun k b hkl hb => Option.some.inj (ha.symm.trans (hkl ▸ hb))
  refine ⟨hinj, fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · show ∃ b g w, mi.globals[k]? = some b ∧ (s.setGlobal a v).globals[b]? = some g ∧
      g.value = Val.i64 w
    obtain ⟨b, g, w, hb, hg, hw⟩ : ∃ b g w, mi.globals[k]? = some b ∧ s.globals[b]? = some g ∧
        g.value = Val.i64 w := hr k hk
    by_cases hkl : k = l
    · obtain ⟨w', hw'⟩ : ∃ w', v = Val.i64 w' := hv.elim (fun h => h.2) (fun h => absurd h.1 (by omega))
      exact ⟨b, { g with value := Val.i64 w' }, w', hb,
        by simp [globals_setGlobal, hba k b hkl hb, hg, hw'], rfl⟩
    · exact ⟨b, g, w, hb, by simp [globals_setGlobal, hab k b hkl hb, hg], hw⟩
  · show ∃ b g w, mi.globals[k]? = some b ∧ (s.setGlobal a v).globals[b]? = some g ∧
      g.value = Val.i32 w ∧ w.toNat < 2
    obtain ⟨b, g, w, hb, hg, hw, hw2⟩ : ∃ b g w, mi.globals[k]? = some b ∧
        s.globals[b]? = some g ∧ g.value = Val.i32 w ∧ w.toNat < 2 := hf k hk1 hk2
    by_cases hkl : k = l
    · obtain ⟨w', hw', hw'2⟩ : ∃ w' : BitVec 32, v = Val.i32 w' ∧ w'.toNat < 2 :=
        hv.elim (fun h => absurd h.1 (by omega)) (fun h => h.2)
      exact ⟨b, { g with value := Val.i32 w' }, w', hb,
        by simp [globals_setGlobal, hba k b hkl hb, hg, hw'], rfl, hw'2⟩
    · exact ⟨b, g, w, hb, by simp [globals_setGlobal, hab k b hkl hb, hg], hw, hw2⟩

theorem keepG_set {mi : ModuleInst} {s : Store H} {l a : Nat} (hl : l < 24)
    (ha : mi.globals[l]? = some a) (v : Val) : keepG mi s (s.setGlobal a v) := by
  refine ⟨by simp [Store.setGlobal], rfl, fun b hb => ?_⟩
  have : a ≠ b := fun h => hb l hl (h ▸ ha)
  simp [globals_setGlobal, this]

theorem keepG_refl (mi : ModuleInst) (s : Store H) : keepG mi s s := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem keepG_trans {mi : ModuleInst} {s₁ s₂ s₃ : Store H} (h₁ : keepG mi s₁ s₂)
    (h₂ : keepG mi s₂ s₃) : keepG mi s₁ s₃ := by
  obtain ⟨l1, e1, f1⟩ := h₁
  obtain ⟨l2, e2, f2⟩ := h₂
  refine ⟨l2.trans l1, ?_, fun a ha => (f2 a ha).trans (f1 a ha)⟩
  rw [e2, e1]

/-- The G representation meets the laws the core uses. -/
theorem repG_laws (mi : ModuleInst) : (repG mi : Rep H).Laws where
  refl s _ := keepG_refl mi s
  trans _ _ _ := keepG_trans
  funcs s s' h := by rw [h.2.1]
  flag s l hok h1 h2 := by
    obtain ⟨-, -, -, -, -, h⟩ := getGf hok h1 h2
    exact (BitVec.lt_def).2 (by simpa [repG] using h)

/-- A write of location `l` (an existing global) in the G representation. -/
theorem setG {mi : ModuleInst} {s : Store H} {l a : Nat} (hok : okG mi s) (hl : l < 24)
    (ha : mi.globals[l]? = some a) (hs : (s.globals[a]?).isSome) (v : Val)
    (hv : (l < 17 ∧ ∃ w, v = Val.i64 w) ∨ (17 ≤ l ∧ ∃ w : BitVec 32, v = Val.i32 w ∧ w.toNat < 2)) :
    okG mi (s.setGlobal a v) ∧ gv (s.setGlobal a v) mi = updL (gv s mi) l (valNum v) ∧
      keepG mi s (s.setGlobal a v) :=
  ⟨okG_set hok hl ha v hv, gv_set hok hl ha hs v, keepG_set hl ha v⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rgetG_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simG 0)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (rgetSpec (repG mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, rfl, hl⟩
  subst hmod
  clear hcode he
  simp [fn, simG, wpc, ctl, enterVC, labelQ, tableVC, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat, Val.i32, Val.i64, Store.global?,
    rgetSpec]
  repeat' (first | exact hl | apply And.intro | intro hj)
  all_goals
    obtain ⟨a', g, h1, h2, h3⟩ := getG hok hl
    rw [hj] at h1
    simp [h1, h2, h3, hj, repG, Val.i64]

rsetG_case rsetG_vc_0 0
rsetG_case rsetG_vc_1 1
rsetG_case rsetG_vc_2 2
rsetG_case rsetG_vc_3 3
rsetG_case rsetG_vc_4 4
rsetG_case rsetG_vc_5 5
rsetG_case rsetG_vc_6 6
rsetG_case rsetG_vc_7 7
rsetG_case rsetG_vc_8 8
rsetG_case rsetG_vc_9 9
rsetG_case rsetG_vc_10 10
rsetG_case rsetG_vc_11 11
rsetG_case rsetG_vc_12 12
rsetG_case rsetG_vc_13 13
rsetG_case rsetG_vc_14 14
rsetG_case rsetG_vc_15 15
rsetG_case rsetG_vc_16 16

set_option maxRecDepth 100000 in
theorem rsetG_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simG 1)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (rsetSpec (repG mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, v, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, v, rfl, hl⟩
  subst hmod
  obtain ⟨k, rfl, hk⟩ : ∃ k, l = BitVec.ofNat 32 k ∧ k < 17 := ⟨l.toNat, by simp, hl⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [rsetG_vc_0 hrs s hok v, rsetG_vc_1 hrs s hok v, rsetG_vc_2 hrs s hok v, rsetG_vc_3 hrs s hok v, rsetG_vc_4 hrs s hok v, rsetG_vc_5 hrs s hok v, rsetG_vc_6 hrs s hok v, rsetG_vc_7 hrs s hok v, rsetG_vc_8 hrs s hok v, rsetG_vc_9 hrs s hok v, rsetG_vc_10 hrs s hok v, rsetG_vc_11 hrs s hok v, rsetG_vc_12 hrs s hok v, rsetG_vc_13 hrs s hok v, rsetG_vc_14 hrs s hok v, rsetG_vc_15 hrs s hok v, rsetG_vc_16 hrs s hok v]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fgetG_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simG 2)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fgetSpec (repG mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, rfl, hl1, hl2⟩
  subst hmod
  clear hcode he
  obtain ⟨a', g, h1, h2, h3, -⟩ := getGf hok hl1 hl2
  obtain ⟨k, rfl, hk1, hk2⟩ : ∃ k, l = BitVec.ofNat 32 k ∧ 17 ≤ k ∧ k < 24 :=
    ⟨l.toNat, by simp, hl1, hl2⟩
  have hk' : (BitVec.ofNat 32 k).toNat = k := by simp; omega
  rw [hk'] at h1 h3
  rcases (show k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [↓tableVC_cons_self, ↓tableVC_cons_of_ne, ↓tableVC_nil_of_le,
      h1, h2, h3, hrs, fn, simG, wpc, ctl, enterVC, labelQ_normal, labelQ_br_zero, labelQ_br_succ, labelQ_ret, labelQ_trap, labelQ_throw, labelQ_tail, popI32, Silmaril.Wasm.Logic.Core.exec1,
      Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost,
      Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat, Val.i32, Val.i64, Store.global?,
      fgetSpec, repG]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fsetG_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simG 3)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fsetSpec (repG mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, v, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, v, rfl, hl1, hl2, hv⟩
  subst hmod
  clear hcode he
  obtain ⟨a', g, h1, h2, -, -⟩ := getGf hok hl1 hl2
  have hset := setG hok hl2 h1 (by simp [h2]) (Val.i32 v) (.inr ⟨hl1, v, rfl, hv⟩)
  obtain ⟨k, rfl, hk1, hk2⟩ : ∃ k, l = BitVec.ofNat 32 k ∧ 17 ≤ k ∧ k < 24 :=
    ⟨l.toNat, by simp, hl1, hl2⟩
  have hk' : (BitVec.ofNat 32 k).toNat = k := by simp; omega
  rw [hk'] at h1 hset
  simp only [valNum_i64, valNum_i32] at hset
  simp only [Val.i64, Val.i32] at hset
  rcases (show k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [↓tableVC_cons_self, ↓tableVC_cons_of_ne, ↓tableVC_nil_of_le,
      h1, h2, hset, hrs, fn, simG, wpc, ctl, enterVC, labelQ_normal, labelQ_br_zero, labelQ_br_succ, labelQ_ret, labelQ_trap, labelQ_throw, labelQ_tail, popI32, Silmaril.Wasm.Logic.Core.exec1,
      Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost,
      Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat, Val.i32, Val.i64, Store.global?,
      Silmaril.Wasm.Logic.Core.popV, fsetSpec, repG]

/-- Six flag writes in a row. -/
theorem set6G {mi : ModuleInst} {s : Store H} (hok : okG mi s) (c p a' z sf o : BitVec 32)
    (hc : c.toNat < 2) (hp : p.toNat < 2) (ha : a'.toNat < 2) (hz : z.toNat < 2)
    (hs : sf.toNat < 2) (ho : o.toNat < 2) :
    ∃ b17 b18 b19 b20 b21 b22, mi.globals[17]? = some b17 ∧ mi.globals[18]? = some b18 ∧
      mi.globals[19]? = some b19 ∧ mi.globals[20]? = some b20 ∧ mi.globals[21]? = some b21 ∧
      mi.globals[22]? = some b22 ∧
      let s' := (((((s.setGlobal b17 (Val.i32 c)).setGlobal b18 (Val.i32 p)).setGlobal b19
        (Val.i32 a')).setGlobal b20 (Val.i32 z)).setGlobal b21 (Val.i32 sf)).setGlobal b22 (Val.i32 o)
      okG mi s' ∧ gv s' mi = upd6 (gv s mi) c p a' z sf o ∧ keepG mi s s' := by
  have step : ∀ (t : Store H) (l : Nat) (v : BitVec 32), okG mi t → 17 ≤ l → l < 24 → v.toNat < 2 →
      ∃ b, mi.globals[l]? = some b ∧ okG mi (t.setGlobal b (Val.i32 v)) ∧
        gv (t.setGlobal b (Val.i32 v)) mi = updL (gv t mi) l (v.setWidth 64) ∧
        keepG mi t (t.setGlobal b (Val.i32 v)) := by
    intro t l v ht h1 h2 hv
    obtain ⟨b, g, hb, hg, -, -⟩ := getGf ht h1 h2
    obtain ⟨o1, o2, o3⟩ := setG ht h2 hb (by simp [hg]) (Val.i32 v) (.inr ⟨h1, v, rfl, hv⟩)
    exact ⟨b, hb, o1, by simpa using o2, o3⟩
  obtain ⟨b17, e17, k17, g17, f17⟩ := step s 17 c hok (by decide) (by decide) hc
  obtain ⟨b18, e18, k18, g18, f18⟩ := step _ 18 p k17 (by decide) (by decide) hp
  obtain ⟨b19, e19, k19, g19, f19⟩ := step _ 19 a' k18 (by decide) (by decide) ha
  obtain ⟨b20, e20, k20, g20, f20⟩ := step _ 20 z k19 (by decide) (by decide) hz
  obtain ⟨b21, e21, k21, g21, f21⟩ := step _ 21 sf k20 (by decide) (by decide) hs
  obtain ⟨b22, e22, k22, g22, f22⟩ := step _ 22 o k21 (by decide) (by decide) ho
  refine ⟨b17, b18, b19, b20, b21, b22, e17, e18, e19, e20, e21, e22, k22, ?_, ?_⟩
  · rw [g22, g21, g20, g19, g18, g17]; rfl
  · exact keepG_trans f17 (keepG_trans f18 (keepG_trans f19 (keepG_trans f20
      (keepG_trans f21 f22))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fset6G_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simG 4)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 6)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fset6Spec (repG mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, c, p, a', z, sf, o, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, c, p, a', z, sf, o, rfl, hc, hp, ha, hz, hs, ho⟩
  subst hmod
  clear hcode he
  obtain ⟨b17, b18, b19, b20, b21, b22, e17, e18, e19, e20, e21, e22, hok', hgv, hkeep⟩ :=
    set6G hok c p a' z sf o hc hp ha hz hs ho
  have hex : ∀ (t : Store H) (b : Nat) (v : Val), (t.globals[b]?).isSome →
      ((t.setGlobal b v).globals[b]?).isSome := fun t b v h => by simpa [globals_setGlobal] using h
  have hg : ∀ l, 17 ≤ l → l < 24 → ∀ b, fi.module.globals[l]? = some b → (s.globals[b]?).isSome :=
    fun l h1 h2 b hb => by
      obtain ⟨b', g, hb', hg, -⟩ := getGf hok h1 h2
      rw [hb] at hb'; cases hb'; simp [hg]
  obtain ⟨g17, hg17⟩ : ∃ g, s.globals[b17]? = some g := Option.isSome_iff_exists.1 (hg 17 (by decide) (by decide) b17 e17)
  obtain ⟨g18, hg18⟩ : ∃ g, s.globals[b18]? = some g := Option.isSome_iff_exists.1 (hg 18 (by decide) (by decide) b18 e18)
  obtain ⟨g19, hg19⟩ : ∃ g, s.globals[b19]? = some g := Option.isSome_iff_exists.1 (hg 19 (by decide) (by decide) b19 e19)
  obtain ⟨g20, hg20⟩ : ∃ g, s.globals[b20]? = some g := Option.isSome_iff_exists.1 (hg 20 (by decide) (by decide) b20 e20)
  obtain ⟨g21, hg21⟩ : ∃ g, s.globals[b21]? = some g := Option.isSome_iff_exists.1 (hg 21 (by decide) (by decide) b21 e21)
  obtain ⟨g22, hg22⟩ : ∃ g, s.globals[b22]? = some g := Option.isSome_iff_exists.1 (hg 22 (by decide) (by decide) b22 e22)
  have hne : ∀ i j bi bj, i < 24 → fi.module.globals[i]? = some bi → fi.module.globals[j]? = some bj →
      i ≠ j → bi ≠ bj := fun i j bi bj hi h1 h2 hij h =>
      hij ((show okG fi.module s from hok).1 i j bi hi h1 (by rw [h]; exact h2))
  have n17_18 : b17 ≠ b18 := hne 17 18 b17 b18 (by decide) e17 e18 (by decide)
  have n17_19 : b17 ≠ b19 := hne 17 19 b17 b19 (by decide) e17 e19 (by decide)
  have n17_20 : b17 ≠ b20 := hne 17 20 b17 b20 (by decide) e17 e20 (by decide)
  have n17_21 : b17 ≠ b21 := hne 17 21 b17 b21 (by decide) e17 e21 (by decide)
  have n17_22 : b17 ≠ b22 := hne 17 22 b17 b22 (by decide) e17 e22 (by decide)
  have n18_19 : b18 ≠ b19 := hne 18 19 b18 b19 (by decide) e18 e19 (by decide)
  have n18_20 : b18 ≠ b20 := hne 18 20 b18 b20 (by decide) e18 e20 (by decide)
  have n18_21 : b18 ≠ b21 := hne 18 21 b18 b21 (by decide) e18 e21 (by decide)
  have n18_22 : b18 ≠ b22 := hne 18 22 b18 b22 (by decide) e18 e22 (by decide)
  have n19_20 : b19 ≠ b20 := hne 19 20 b19 b20 (by decide) e19 e20 (by decide)
  have n19_21 : b19 ≠ b21 := hne 19 21 b19 b21 (by decide) e19 e21 (by decide)
  have n19_22 : b19 ≠ b22 := hne 19 22 b19 b22 (by decide) e19 e22 (by decide)
  have n20_21 : b20 ≠ b21 := hne 20 21 b20 b21 (by decide) e20 e21 (by decide)
  have n20_22 : b20 ≠ b22 := hne 20 22 b20 b22 (by decide) e20 e22 (by decide)
  have n21_22 : b21 ≠ b22 := hne 21 22 b21 b22 (by decide) e21 e22 (by decide)
  simp only [Val.i32] at hok' hgv hkeep
  simp only [Func.body, fn, simG, Fin.isValue, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reducePow, Fin.zero_eta, Option.getD_some, hrs, fset6Spec, repG, Val.i32, List.cons.injEq,
      Val.num.injEq, numI32_inj, and_true, and_imp, Frame.forCall, List.map_cons, List.map_nil,
      Func.locals, List.append_nil, wpc, ctl, Wasm.Logic.Core.exec1, List.reverse_nil,
      Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.ofNat_pos, Option.map_some, List.reverse_cons, List.nil_append, Wasm.Logic.Core.popV,
      Store.global?, Nat.reduceMod, e17, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      hg17, Nat.one_mod, Nat.one_lt_ofNat, e18, globals_setGlobal, n17_18, ↓reduceIte, hg18, e19,
      n18_19, n17_19, hg19, e20, n19_20, n18_20, n17_20, hg20, e21, n20_21, n19_21, n18_21, n17_21,
      hg21, Nat.lt_add_one, e22, n21_22, n20_22, n19_22, n18_22, n17_22, hg22, fnPost, hok', hgv,
      hkeep, true_and]
  rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  rfl

end Silmaril.Sim.X86Real
