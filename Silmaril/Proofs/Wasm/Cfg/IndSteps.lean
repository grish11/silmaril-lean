module

public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Abstract.CallRes.Thms
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift

@[expose] public section

/-!
# Core runs of `table.get` and `ref.cast` under values (every profile and host)

The two instructions `call_indirect x y` unfolds into before its `call_ref y`. Their first Core
step is a family rule on the top operand (`famStep_tableGet_inv`, `famStep_refCast_inv`), after
which the configuration is values (stuck) or a trap after values (which only steps to a trap, in
the same store and frame). So a Core run of either to values or to a trap is the one `CallRes`
predicts, at any profile and host.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem vals_snoc_two {vs : List Val} {p q d : Admin} (h : vals vs ++ [p] = [q, d]) :
    ∃ v, vs = [v] ∧ v.toAdmin = q ∧ p = d := by
  rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
  · simp [vals] at h
  · simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, and_true] at h
    exact ⟨v, rfl, h.1, h.2⟩
  · simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨-, -, h3⟩ := h
    cases vs <;> simp at h3

theorem toAdmin_aconst {v : Val} {a : AddrType} {i : BitVec a.intType.width}
    (h : v.toAdmin = aconst a i) : v = .num ⟨.int a.intType, i⟩ := by
  have h1 := congrArg Admin.val? h
  rw [Admin.val?_toAdmin] at h1
  exact Option.some.inj h1

theorem toAdmin_ref {v : Val} {r : Ref} (h : v.toAdmin = .ref r) : v = .ref r := by
  have h1 := congrArg Admin.val? h
  rw [Admin.val?_toAdmin] at h1
  exact Option.some.inj h1

set_option linter.unusedTactic false in
/-- **The first step of `table.get`**, inverted. -/
theorem famStep_tableGet_inv {s : Store H} {f : Frame} {vs : List Val} {x : TableIdx}
    {c₀ : Config H} (h : FamStep P ⟨s, f, vals vs ++ [.plain (.tableGet x)]⟩ c₀) :
    ∃ a i ta ti, vs = [.num ⟨.int (AddrType.intType a), i⟩] ∧ s.table? f x = some (ta, ti) ∧
      ((∃ r, ti.refs[i.toNat]? = some r ∧ c₀ = ⟨s, f, [.ref r]⟩) ∨
        (ti.refs.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩)) := by
  generalize hc : (⟨s, f, vals vs ++ [.plain (.tableGet x)]⟩ : Config H) = c at h
  cases h with
  | table h =>
    cases h <;> simp only [Config.mk.injEq] at hc <;>
      first
        | (have h2 := congrArg List.getLast? hc.2.2; simp at h2; done)
        | skip
    · rename_i a i ta ti ht hl
      obtain ⟨rfl, rfl, hc⟩ := hc
      obtain ⟨v, rfl, hv, hx⟩ := vals_snoc_two hc
      simp only [Admin.plain.injEq, Instr.tableGet.injEq] at hx
      subst hx
      exact ⟨a, i, ta, ti, by rw [toAdmin_aconst hv], ht, .inr ⟨hl, rfl⟩⟩
    · rename_i a i ta ti r ht hr
      obtain ⟨rfl, rfl, hc⟩ := hc
      obtain ⟨v, rfl, hv, hx⟩ := vals_snoc_two hc
      simp only [Admin.plain.injEq, Instr.tableGet.injEq] at hx
      subst hx
      exact ⟨a, i, ta, ti, by rw [toAdmin_aconst hv], ht, .inl ⟨r, hr, rfl⟩⟩
  | _ =>
    rename_i h
    cases h <;>
    (simp only [Config.mk.injEq] at hc
     have h2 := congrArg List.getLast? hc.2.2
     simp at h2)

set_option linter.unusedTactic false in
/-- **The first step of `ref.cast`**, inverted. -/
theorem famStep_refCast_inv {s : Store H} {f : Frame} {vs : List Val} {rt : RefType}
    {c₀ : Config H} (h : FamStep P ⟨s, f, vals vs ++ [.plain (.refCast rt)]⟩ c₀) :
    ∃ r, vs = [.ref r] ∧ ((RefOk s r (f.module.instRef rt) ∧ c₀ = ⟨s, f, [.ref r]⟩) ∨
      (¬ RefOk s r (f.module.instRef rt) ∧ c₀ = ⟨s, f, [.trap]⟩)) := by
  generalize hc : (⟨s, f, vals vs ++ [.plain (.refCast rt)]⟩ : Config H) = c at h
  cases h with
  | reference h =>
    cases h <;> simp only [Config.mk.injEq] at hc <;>
      first
        | (have h2 := congrArg List.getLast? hc.2.2; simp at h2; done)
        | skip
    · rename_i r rt' hok
      obtain ⟨rfl, rfl, hc⟩ := hc
      obtain ⟨v, rfl, hv, hx⟩ := vals_snoc_two hc
      simp only [Admin.plain.injEq, Instr.refCast.injEq] at hx
      subst hx
      exact ⟨r, by rw [toAdmin_ref hv], .inl ⟨hok, rfl⟩⟩
    · rename_i r rt' hok
      obtain ⟨rfl, rfl, hc⟩ := hc
      obtain ⟨v, rfl, hv, hx⟩ := vals_snoc_two hc
      simp only [Admin.plain.injEq, Instr.refCast.injEq] at hx
      subst hx
      exact ⟨r, by rw [toAdmin_ref hv], .inr ⟨hok, rfl⟩⟩
  | _ =>
    rename_i h
    cases h <;>
    (simp only [Config.mk.injEq] at hc
     have h2 := congrArg List.getLast? hc.2.2
     simp at h2)

/-! ## Forced runs -/

theorem steps_of_vals {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (h : Steps P host ⟨s, f, vals vs⟩ c) : c = ⟨s, f, vals vs⟩ := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs Sim.Step.not_vals

/-- A trap after values only steps to a trap after (fewer) values, in place. -/
theorem steps_of_trapVals {s : Store H} {f : Frame} {w : List Val} {c : Config H}
    (h : Steps P host ⟨s, f, vals w ++ [.trap]⟩ c) :
    c.store = s ∧ c.frame = f ∧ ∃ w', c.code = vals w' ++ [.trap] := by
  induction h with
  | refl => exact ⟨rfl, rfl, w, rfl⟩
  | @tail c₁ c₂ _ hs ih =>
    obtain ⟨h1, h2, w', h3⟩ := ih
    obtain ⟨s₁, f₁, x₁⟩ := c₁
    simp only at h1 h2 h3; subst h1 h2 h3
    obtain ⟨w'', rfl, -⟩ := Step.trap_vals_inv hs
    exact ⟨rfl, rfl, w'', rfl⟩

theorem trapVals_ne_vals {w vs : List Val} : vals w ++ [Admin.trap] ≠ vals vs := by
  intro h
  have : Admin.trap ∈ vals vs := by rw [← h]; simp
  obtain ⟨v, -, hv⟩ := List.mem_map.1 this
  have h1 := congrArg Admin.val? hv
  rw [Admin.val?_toAdmin] at h1
  simp [Admin.val?] at h1

theorem vals_ne_trap {vs : List Val} : vals vs ≠ [Admin.trap] := by
  simpa using (trapVals_ne_vals (w := [])).symm

theorem snoc_plain_ne_vals {us vs : List Val} {i : Instr} (hi : (Admin.plain i).val? = none) :
    vals us ++ [Admin.plain i] ≠ vals vs := by
  intro h
  have : Admin.plain i ∈ vals vs := by rw [← h]; simp
  obtain ⟨v, -, hv⟩ := List.mem_map.1 this
  rw [← hv, Admin.val?_toAdmin] at hi
  cases hi

theorem snoc_plain_ne_trap {us : List Val} {i : Instr} :
    vals us ++ [Admin.plain i] ≠ [Admin.trap] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- The first step of a Core run of a non-control instruction under values, to another code. -/
theorem first_famStep {s s' : Store H} {f f' : Frame} {us : List Val} {i : Instr}
    {X : List Admin} (hk : SingleThreaded.Det.famOf (.plain i) ≠ .control)
    (h : Steps P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', X⟩)
    (hne : vals us ++ [.plain i] ≠ X) :
    ∃ ws vs c₀, us = ws ++ vs ∧ FamStep P ⟨s, f, vals vs ++ [.plain i]⟩ c₀ ∧
      Steps P host ⟨c₀.store, c₀.frame, vals ws ++ c₀.code⟩ ⟨s', f', X⟩ := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c₁, h1, h2⟩
  · exact absurd (congrArg Config.code he) hne
  · obtain ⟨ws, vs, c₀, rfl, hf, rfl⟩ := Step.noncontrol_vals_inv hk h1
    exact ⟨ws, vs, c₀, rfl, hf, h2⟩

theorem famOf_tableGet' (x : TableIdx) :
    SingleThreaded.Det.famOf (.plain (.tableGet x)) ≠ .control := by
  simp [SingleThreaded.Det.famOf]

theorem famOf_refCast' (rt : RefType) :
    SingleThreaded.Det.famOf (.plain (.refCast rt)) ≠ .control := by
  simp [SingleThreaded.Det.famOf]

/-- **`table.get` to values**: it read the entry at the index on top, in place. -/
theorem tableGet_vals_inv {s s₁ : Store H} {f f₁ : Frame} {us vs₁ : List Val} {x : TableIdx}
    (h : Steps P host ⟨s, f, vals us ++ [.plain (.tableGet x)]⟩ ⟨s₁, f₁, vals vs₁⟩) :
    ∃ W a i ta ti r, us = W ++ [.num ⟨.int (AddrType.intType a), i⟩] ∧
      s.table? f x = some (ta, ti) ∧ ti.refs[i.toNat]? = some r ∧ s₁ = s ∧ f₁ = f ∧
      vs₁ = W ++ [.ref r] := by
  obtain ⟨W, vs, c₀, rfl, hf, hrest⟩ := first_famStep (famOf_tableGet' x) h
    (snoc_plain_ne_vals (by simp [Admin.val?]))
  obtain ⟨a, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_tableGet_inv hf
  · have he := steps_of_vals (vs := W ++ [.ref r]) (by simpa [vals_append, Val.toAdmin] using hrest)
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, hv⟩ := he
    exact ⟨W, a, i, ta, ti, r, rfl, ht, hr, rfl, rfl, Sim.vals_injective hv⟩
  · obtain ⟨-, -, w', hw⟩ := steps_of_trapVals hrest
    exact absurd hw.symm trapVals_ne_vals

/-- **`table.get` to a trap**: the index on top is out of bounds, in place. -/
theorem tableGet_trap_inv {s s₁ : Store H} {f f₁ : Frame} {us : List Val} {x : TableIdx}
    (h : Steps P host ⟨s, f, vals us ++ [.plain (.tableGet x)]⟩ ⟨s₁, f₁, [.trap]⟩) :
    ∃ W a i ta ti, us = W ++ [.num ⟨.int (AddrType.intType a), i⟩] ∧
      s.table? f x = some (ta, ti) ∧ ti.refs.length ≤ i.toNat ∧ s₁ = s ∧ f₁ = f := by
  obtain ⟨W, vs, c₀, rfl, hf, hrest⟩ := first_famStep (famOf_tableGet' x) h snoc_plain_ne_trap
  obtain ⟨a, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨hl, rfl⟩⟩ := famStep_tableGet_inv hf
  · have he := steps_of_vals (vs := W ++ [.ref r]) (by simpa [vals_append, Val.toAdmin] using hrest)
    simp only [Config.mk.injEq] at he
    exact absurd he.2.2.symm vals_ne_trap
  · obtain ⟨h1, h2, -⟩ := steps_of_trapVals hrest
    exact ⟨W, a, i, ta, ti, rfl, ht, hl, h1, h2⟩

/-- **`ref.cast` to values**: the reference on top passes the cast, in place. -/
theorem refCast_vals_inv {s s₁ : Store H} {f f₁ : Frame} {us vs₁ : List Val} {rt : RefType}
    (h : Steps P host ⟨s, f, vals us ++ [.plain (.refCast rt)]⟩ ⟨s₁, f₁, vals vs₁⟩) :
    ∃ W r, us = W ++ [.ref r] ∧ RefOk s r (f.module.instRef rt) ∧ s₁ = s ∧ f₁ = f ∧
      vs₁ = us := by
  obtain ⟨W, vs, c₀, rfl, hf, hrest⟩ := first_famStep (famOf_refCast' rt) h
    (snoc_plain_ne_vals (by simp [Admin.val?]))
  obtain ⟨r, rfl, ⟨hok, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_refCast_inv hf
  · have he := steps_of_vals (vs := W ++ [.ref r]) (by simpa [vals_append, Val.toAdmin] using hrest)
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, hv⟩ := he
    exact ⟨W, r, rfl, hok, rfl, rfl, Sim.vals_injective hv⟩
  · obtain ⟨-, -, w', hw⟩ := steps_of_trapVals hrest
    exact absurd hw.symm trapVals_ne_vals

/-- **`ref.cast` to a trap**: the reference on top fails the cast, in place. -/
theorem refCast_trap_inv {s s₁ : Store H} {f f₁ : Frame} {us : List Val} {rt : RefType}
    (h : Steps P host ⟨s, f, vals us ++ [.plain (.refCast rt)]⟩ ⟨s₁, f₁, [.trap]⟩) :
    ∃ W r, us = W ++ [.ref r] ∧ ¬ RefOk s r (f.module.instRef rt) ∧ s₁ = s ∧ f₁ = f := by
  obtain ⟨W, vs, c₀, rfl, hf, hrest⟩ := first_famStep (famOf_refCast' rt) h snoc_plain_ne_trap
  obtain ⟨r, rfl, ⟨hok, rfl⟩ | ⟨hok, rfl⟩⟩ := famStep_refCast_inv hf
  · have he := steps_of_vals (vs := W ++ [.ref r]) (by simpa [vals_append, Val.toAdmin] using hrest)
    simp only [Config.mk.injEq] at he
    exact absurd he.2.2.symm vals_ne_trap
  · obtain ⟨h1, h2, -⟩ := steps_of_trapVals hrest
    exact ⟨W, r, rfl, hok, h1, h2⟩

end Silmaril.Wasm.Cfg.Proofs.Region
