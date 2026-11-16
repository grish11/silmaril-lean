module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.WasmBranch.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem signed_zero_iff (q : BitVec 32) : q.toInt = 0 ↔ q = 0 := by
  constructor
  · intro h
    have he := congrArg (BitVec.ofInt 32) h
    exact (BitVec.ofInt_toInt).symm.trans he
  · rintro rfl
    rfl

/-- Explicit signed bounds suffice for the Int/i32 round trip. The original
conditional KORE relation continues to allow arbitrary Int values. -/
theorem signed_representation (x : Int) (lo : -(2^31) ≤ x) (hi : x < 2^31) :
    (BitVec.ofInt 32 x).toInt = x :=
  BitVec.toInt_ofInt_eq_self (by decide) lo hi

/-- All successors of the represented source entry have exactly the selected
state, with the original tail/value/counter; no native execution premise. -/
theorem source_step_iff (L : Layout) (tail : List String) (q k : BitVec 32)
    (d : Conditional.Config) :
    Conditional.Step L.rules (source L .entry tail q k) d ↔
      d = source L (selected q) tail q k := by
  constructor
  · show Conditional.Step L.rules (source L .entry tail q k) d →
      d = source L (selected q) tail q k
    intro h
    obtain ⟨r, hr, v, hc, hg, he, hd⟩ := (Conditional.step_iff _ _ _).mp h
    have hr' : r = ⟨L.entry, L.zero, .zero⟩ ∨ r = ⟨L.entry, L.nonzero, .nonzero⟩ := by
      simpa only [Layout.rules, List.mem_cons, List.not_mem_nil, or_false] using hr
    have hv : q.toInt = v.x := congrArg Conditional.Config.val he
    have hn : k.toInt = v.counter := congrArg Conditional.Config.counter he
    rcases hr' with rfl | rfl
    · show d = source L (selected q) tail q k
      have ht : tail = v.tail := (List.cons.inj (congrArg Conditional.Config.code he)).2
      have hz : q = 0 := (signed_zero_iff q).mp (hv.trans (by
        simpa only [Guard.Holds, Guard.eval, intEqual, decide_eq_true_eq] using hg))
      simpa only [selected, ite_eq_left hz, source, Layout.name, Rule.afterConfig,
        ← ht, ← hn, ← hc, ← hv] using hd
    · show d = source L (selected q) tail q k
      have ht : tail = v.tail := (List.cons.inj (congrArg Conditional.Config.code he)).2
      have hz : q ≠ 0 := by
        intro hq
        have hv0 : v.x = 0 := hv.symm.trans ((signed_zero_iff q).mpr hq)
        simp [Guard.Holds, Guard.eval, intEqual, hv0] at hg
      simpa only [selected, ite_eq_right hz, source, Layout.name, Rule.afterConfig,
        ← ht, ← hn, ← hc, ← hv] using hd
  · show d = source L (selected q) tail q k →
      Conditional.Step L.rules (source L .entry tail q k) d
    rintro rfl
    by_cases hz : q = 0
    · show Conditional.Step L.rules (source L .entry tail q k) (source L (selected q) tail q k)
      have hv : q.toInt = 0 := (signed_zero_iff q).mpr hz
      simpa only [selected, ite_eq_left hz, source, Layout.name, Rule.beforeConfig, Rule.afterConfig] using
        (Conditional.Step.rule (rules := L.rules) ⟨L.entry, L.zero, .zero⟩
          (by simp [Layout.rules]) ⟨tail, q.toInt, q.toInt, k.toInt⟩ rfl
          (by simp [Guard.Holds, Guard.eval, intEqual, hv]))
    · show Conditional.Step L.rules (source L .entry tail q k) (source L (selected q) tail q k)
      have hv : q.toInt ≠ 0 := fun h => hz ((signed_zero_iff q).mp h)
      simpa only [selected, ite_eq_right hz, source, Layout.name, Rule.beforeConfig, Rule.afterConfig] using
        (Conditional.Step.rule (rules := L.rules) ⟨L.entry, L.nonzero, .nonzero⟩
          (by simp [Layout.rules]) ⟨tail, q.toInt, q.toInt, k.toInt⟩ rfl
          (by simp [Guard.Holds, Guard.eval, intEqual, hv]))

/-- The retained distinct source names let an observer recover the zero test. -/
theorem selected_name_zero_iff (L : Layout) (q : BitVec 32) :
    L.name (selected q) = L.zero ↔ q = 0 := by
  by_cases hz : q = 0
  · have hs : selected q = .zero := ite_eq_left hz
    rw [hs]
    exact ⟨fun _ => hz, fun _ => rfl⟩
  · have hs : selected q = .nonzero := ite_eq_right hz
    rw [hs]
    exact ⟨fun he => False.elim (L.zero_ne_nonzero he.symm), fun he => False.elim (hz he)⟩

/-- Read the represented source value using the existing open-expression compiler,
then select the actual native branch. Bodies and continuation are unexecuted. -/
theorem native_steps {H : Type} (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String)
    (rest : List Admin) (valueLocal : LocalIdx) (q : BitVec 32)
    (hvalue : Silmaril.Wasm.Logic.Core.localVal? f valueLocal = some (Val.i32 q)) :
    Steps P host (native L .entry s f older tail rest valueLocal)
      (native L (selected q) s f older tail rest valueLocal) := by
  let middle : Core.Config H := ⟨s, f, vals older ++
    [constI32 q, .plain (.if_ L.blockType L.nonzeroBody L.zeroBody)] ++ L.tailCode tail ++ rest⟩
  have read : Steps P host (native L .entry s f older tail rest valueLocal) middle := by
    have h := Reachability.WasmExpr.executes P host s f older.reverse
      (fun _ : Fin 1 => valueLocal) (fun _ => q)
      (.var 0 : Reachability.WasmExpr.Expr 1)
      ([.plain (.if_ L.blockType L.nonzeroBody L.zeroBody)] ++ L.tailCode tail ++ rest)
      (fun _ => hvalue)
    change Steps P host
      ⟨s, f, vals older.reverse.reverse ++ expression [.localGet valueLocal] ++
        ([.plain (.if_ L.blockType L.nonzeroBody L.zeroBody)] ++ L.tailCode tail ++ rest)⟩
      ⟨s, f, vals (Val.i32 q :: older.reverse).reverse ++
        ([.plain (.if_ L.blockType L.nonzeroBody L.zeroBody)] ++ L.tailCode tail ++ rest)⟩ at h
    simpa only [native, middle, List.reverse_reverse, List.reverse_cons, vals, expression,
      constI32, List.map_cons, List.map_nil, List.map_append, List.append_assoc,
      List.cons_append, List.nil_append] using h
  have branch : Steps P host middle (native L (selected q) s f older tail rest valueLocal) := by
    by_cases hz : q = 0
    · subst q
      simpa [middle, native, selected, List.append_assoc] using
        (Core.Steps.ctxtInstrs (vs := older) (rest := L.tailCode tail ++ rest)
          (Core.Step.steps (Core.Step.ifFalse (P := P) (host := host)
            (s := s) (f := f) (bt := L.blockType) (b₁ := L.nonzeroBody) (b₂ := L.zeroBody))))
    · have hs : selected q = .nonzero := ite_eq_right hz
      simpa only [middle, native, hs, List.append_assoc] using
        (Core.Steps.ctxtInstrs (vs := older) (rest := L.tailCode tail ++ rest)
          (Core.Step.steps (Core.Step.ifTrue (P := P) (host := host)
            (s := s) (f := f) (bt := L.blockType) (b₁ := L.nonzeroBody) (b₂ := L.zeroBody) hz)))
  exact read.trans branch

/-- Every represented source step has an actual native run to a related exit.
Local agreement is preserved because the native store/frame stay unchanged. -/
theorem related_step {H : Type} (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32)
    (c d : Conditional.Config) (w : Core.Config H)
    (hr : Related L .entry s f older tail rest valueLocal counterLocal q k c w)
    (hs : Conditional.Step L.rules c d) :
    ∃ w', Steps P host w w' ∧
      Related L (selected q) s f older tail rest valueLocal counterLocal q k d w' := by
  rcases hr with ⟨rfl, rfl, agree⟩
  exact ⟨_, native_steps L P host s f older tail rest valueLocal q agree.1,
    (source_step_iff L tail q k d).mp hs, rfl, agree⟩

/-- Existing exact finite-execution matching bridge, applied to the related exit. -/
theorem compiled_valid {H : Type} (L : Layout) (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32)
    (agree : LocalsAgree f valueLocal counterLocal q k) :
    Matching.FixedPoint.Sentence.Satisfies
      (Reachability.WasmExpr.predicateModel P host (native L .entry s f older tail rest valueLocal)
        (fun w => Related L (selected q) s f older tail rest valueLocal counterLocal q k
          (source L (selected q) tail q k) w))
      (Reachability.encode () (Reachability.atomRule .finite false true)) :=
  (Reachability.WasmExpr.compiled_iff_steps P host _ _).mpr
    ⟨_, native_steps L P host s f older tail rest valueLocal q agree.1, rfl, rfl, agree⟩

end Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
