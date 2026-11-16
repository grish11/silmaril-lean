module

public import Silmaril.Proofs.Wasm.Cfg.BridgeBwd
public import Silmaril.Proofs.Wasm.Cfg.RegionTailRes
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Abstract.CallRes.Thms

@[expose] public section

/-!
# The backward bridge: `return_call_indirect` that does not reach a callee (proofs)

In the region semantics `return_call_indirect x y` runs as `table.get x; ref.cast (ref null y);
return_call_ref y`, the first two by Core reduction. At the deterministic profile without host,
host-free normal forms are unique (`eq_of_steps_of_nf`), so the Core runs of `table.get` and
`ref.cast` are the ones `CallRes` predicts (`tableGet_steps`, `refCast_steps`, …): the first Core
step is inverted (`famStep_tableGet_inv`, `famStep_refCast_inv`) and the rest is forced.

`run_rci_inv`: a region run of `return_call_indirect` whose outcome is not a pending tail call of a
function resolves the index to no callee (`CallRes.IndRes … none`) and ends in a trap or a
pending tail call of null, in the same store and frame.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract.CallRes

variable {H : Type} {C : Abstract.CallRel H}

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

variable {P : Profile}

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

/-! ## Forced Core runs -/

section Forced

variable {o : SingleThreaded.GrowOracle}

local notation "PP" => SingleThreaded.profile o

theorem steps_nf_eq {c c' : Config H} (hc : ∀ d, ¬ Step PP Interp.noHostX c d)
    (h : Steps PP Interp.noHostX c c') : c' = c := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hc _)

theorem uniq {c c₁ c₂ : Config H} (h₁ : Steps PP Interp.noHostX c c₁)
    (h₂ : Steps PP Interp.noHostX c c₂) (n₁ : ∀ d, ¬ Step PP Interp.noHostX c₁ d)
    (n₂ : ∀ d, ¬ Step PP Interp.noHostX c₂ d) : c₁ = c₂ :=
  SingleThreaded.Exec.BehaviourRefinement.eq_of_steps_of_nf (o := o) h₁ h₂ n₁ n₂

theorem vals_nf (s : Store H) (f : Frame) (vs : List Val) :
    ∀ d, ¬ Step PP Interp.noHostX ⟨s, f, vals vs⟩ d := fun _ => Sim.Step.not_vals

theorem trap_nf (s : Store H) (f : Frame) : ∀ d, ¬ Step PP Interp.noHostX ⟨s, f, [.trap]⟩ d :=
  fun _ => Step.trap_stuck

theorem vals_ne_trap {vs : List Val} : vals vs ≠ [.trap] := by
  intro h
  have : Admin.trap ∈ vals vs := by rw [h]; simp
  obtain ⟨v, -, hv⟩ := List.mem_map.1 this
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv

theorem vals_ne_snoc_plain {vs ws : List Val} {i : Instr} (hi : (Admin.plain i).val? = none) :
    vals ws ++ [.plain i] ≠ vals vs := by
  intro h
  have : Admin.plain i ∈ vals vs := by rw [← h]; simp
  obtain ⟨v, -, hv⟩ := List.mem_map.1 this
  rw [← hv, Admin.val?_toAdmin] at hi
  cases hi

theorem trap_ne_snoc_plain {ws : List Val} {i : Instr} : vals ws ++ [.plain i] ≠ [.trap] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

theorem snoc_ref_ne_trap (ws : List Val) (r : Ref) : vals ws ++ [.ref r] ≠ [.trap] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- The first step of a Core run of a non-control instruction under values, to a normal form
other than the start. -/
theorem first_step {s s' : Store H} {f f' : Frame} {us : List Val} {i : Instr} {X : List Admin}
    (hk : SingleThreaded.Det.famOf (.plain i) ≠ .control)
    (h : Steps PP Interp.noHostX ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', X⟩)
    (hne : vals us ++ [.plain i] ≠ X) :
    ∃ ws vs c₀, us = ws ++ vs ∧ FamStep PP ⟨s, f, vals vs ++ [.plain i]⟩ c₀ ∧
      Steps PP Interp.noHostX ⟨c₀.store, c₀.frame, vals ws ++ c₀.code⟩ ⟨s', f', X⟩ := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c₁, h1, h2⟩
  · exact absurd (congrArg Config.code he) hne
  · obtain ⟨ws, vs, c₀, rfl, hf, rfl⟩ := Step.noncontrol_vals_inv hk h1
    exact ⟨ws, vs, c₀, rfl, hf, h2⟩

/-- **`return_call_indirect`, backwards**: a region run resolves the index under the top as
`CallRes.IndRes` does, in the same store and frame. Without a callee it traps or reaches a pending
tail call of null; with one, it ends in a pending tail call of that callee over the values under
the index. -/
theorem run_rci_cases {s s' : Store H} {f f' : Frame} {us : List Val} {x : TableIdx}
    {y : TypeIdx} {out : Region.Out}
    (h : RunC PP Interp.noHostX C s f us [.plain (.returnCallIndirect x y)] s' f' out) :
    ∃ W a i, us = W ++ [.num ⟨.int a.intType, i⟩] ∧ s' = s ∧ f' = f ∧
      ((IndRes s f x y a i none ∧ (out = .trap ∨ ∃ c, out = .tailNull W c)) ∨
        ∃ fa c, IndRes s f x y a i (some fa) ∧ out = .tail W fa c) := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | returnCallIndirect h₁ =>
    rcases Proofs.Region.run_simple_inv (Proofs.Region.famOf_tableGet x) h₁ with
      ⟨s₁, f₁, vs₁, hst, h₂⟩ | ⟨rfl, hst⟩
    · obtain ⟨ws, vs, c₀, rfl, hf, hrest⟩ := first_step (Proofs.Region.famOf_tableGet x) hst
        (vals_ne_snoc_plain (by simp [Admin.val?]))
      obtain ⟨a, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨hl, rfl⟩⟩ := famStep_tableGet_inv hf
      · have he := steps_nf_eq (by rw [← Proofs.Region.vals_snoc_ref]; exact vals_nf (o := o) s f (ws ++ [.ref r])) hrest
        simp only [Config.mk.injEq] at he
        obtain ⟨hs, hf, hv⟩ := he
        subst s₁ f₁
        have hv' : vs₁ = ws ++ [.ref r] := Sim.vals_injective (by rw [Proofs.Region.vals_snoc_ref]; exact hv)
        subst hv'
        rcases Proofs.Region.run_simple_inv (Proofs.Region.famOf_refCast _) h₂ with
          ⟨s₂, f₂, vs₂, hst₂, h₃⟩ | ⟨rfl, hst₂⟩
        · obtain ⟨ws', vs', c₀', he', hf', hrest'⟩ := first_step (Proofs.Region.famOf_refCast _)
            hst₂ (vals_ne_snoc_plain (by simp [Admin.val?]))
          obtain ⟨r', rfl, ⟨hok, rfl⟩ | ⟨hok, rfl⟩⟩ := famStep_refCast_inv hf'
          · obtain ⟨rfl, hrr⟩ := List.append_inj' he' rfl
            simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
            subst hrr
            have he := steps_nf_eq (by rw [← Proofs.Region.vals_snoc_ref]; exact vals_nf (o := o) s f (ws ++ [.ref r])) hrest'
            simp only [Config.mk.injEq] at he
            obtain ⟨hs, hf, hv⟩ := he
            subst s₂ f₂
            have hv' : vs₂ = ws ++ [.ref r] := Sim.vals_injective (by rw [Proofs.Region.vals_snoc_ref]; exact hv)
            subst hv'
            generalize hW : ws ++ [Val.ref r] = W at h₃
            cases h₃ with
            | returnCallRef hc =>
              obtain ⟨rfl, hrr⟩ := List.append_inj' hW rfl
              simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
              subst hrr
              exact ⟨ws, a, i, rfl, rfl, rfl, .inr ⟨_, _, .func ht hr hok, rfl⟩⟩
            | returnCallRefNull hc =>
              obtain ⟨rfl, hrr⟩ := List.append_inj' hW rfl
              simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
              subst hrr
              exact ⟨ws, a, i, rfl, rfl, rfl, .inl ⟨.null ht hr hok, .inr ⟨_, rfl⟩⟩⟩
            | val hv => simp [Admin.val?] at hv
            | simple hi => simp [SingleThreaded.Det.famOf] at hi
            | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
            | brData hb => cases hb
          · obtain ⟨rfl, hrr⟩ := List.append_inj' he' rfl
            simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
            subst hrr
            exact absurd (congrArg Config.code (uniq hrest'
              (by simpa using Proofs.Region.steps_trap (P := PP) (host := Interp.noHostX) s f ws [])
              (vals_nf (o := o) _ _ _) (trap_nf (o := o) _ _))) vals_ne_trap
        · obtain ⟨ws', vs', c₀', he', hf', hrest'⟩ := first_step (Proofs.Region.famOf_refCast _)
            hst₂ trap_ne_snoc_plain
          obtain ⟨r', rfl, ⟨hok, rfl⟩ | ⟨hok, rfl⟩⟩ := famStep_refCast_inv hf'
          · obtain ⟨rfl, hrr⟩ := List.append_inj' he' rfl
            simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
            subst hrr
            have he := steps_nf_eq (by rw [← Proofs.Region.vals_snoc_ref]; exact vals_nf (o := o) s f (ws ++ [.ref r])) hrest'
            exact absurd (congrArg Config.code he).symm (snoc_ref_ne_trap ws r)
          · obtain ⟨rfl, hrr⟩ := List.append_inj' he' rfl
            simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
            subst hrr
            have he := uniq hrest'
              (by simpa using Proofs.Region.steps_trap (P := PP) (host := Interp.noHostX) s f ws [])
              (trap_nf (o := o) _ _) (trap_nf (o := o) _ _)
            simp only [Config.mk.injEq] at he
            obtain ⟨hs', hf', -⟩ := he
            exact ⟨ws, a, i, rfl, hs', hf', .inl ⟨.castFail ht hr hok, .inl rfl⟩⟩
      · exact absurd (congrArg Config.code (uniq hrest
          (by simpa using Proofs.Region.steps_trap (P := PP) (host := Interp.noHostX) s f ws [])
          (vals_nf (o := o) _ _ _) (trap_nf (o := o) _ _))) vals_ne_trap
    · obtain ⟨ws, vs, c₀, rfl, hf, hrest⟩ := first_step (Proofs.Region.famOf_tableGet x) hst
        trap_ne_snoc_plain
      obtain ⟨a, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨hl, rfl⟩⟩ := famStep_tableGet_inv hf
      · have he := steps_nf_eq (by rw [← Proofs.Region.vals_snoc_ref]; exact vals_nf (o := o) s f (ws ++ [.ref r])) hrest
        exact absurd (congrArg Config.code he).symm (snoc_ref_ne_trap ws r)
      · have he := uniq hrest
          (by simpa using Proofs.Region.steps_trap (P := PP) (host := Interp.noHostX) s f ws [])
          (trap_nf (o := o) _ _) (trap_nf (o := o) _ _)
        simp only [Config.mk.injEq] at he
        obtain ⟨hs', hf', -⟩ := he
        exact ⟨ws, a, i, rfl, hs', hf', .inl ⟨.oob ht hl, .inl rfl⟩⟩

/-- **`return_call_indirect` without a callee, backwards**: a region run whose outcome is not a
pending tail call of a function resolves the index to no callee and traps, or reaches a pending
tail call of null, in the same store and frame. -/
theorem run_rci_inv {s s' : Store H} {f f' : Frame} {us : List Val} {x : TableIdx}
    {y : TypeIdx} {out : Region.Out}
    (h : RunC PP Interp.noHostX C s f us [.plain (.returnCallIndirect x y)] s' f' out)
    (hnt : ∀ W a c, out ≠ .tail W a c) :
    ∃ W a i, us = W ++ [.num ⟨.int a.intType, i⟩] ∧ IndRes s f x y a i none ∧ s' = s ∧
      f' = f ∧ (out = .trap ∨ ∃ c, out = .tailNull W c) := by
  obtain ⟨W, a, i, rfl, rfl, rfl, ⟨hres, ho⟩ | ⟨fa, c, -, rfl⟩⟩ := run_rci_cases h
  · exact ⟨W, a, i, rfl, hres, rfl, rfl, ho⟩
  · exact absurd rfl (hnt _ _ _)

end Forced

end Silmaril.Wasm.Cfg.Proofs.Bridge
