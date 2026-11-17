module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Defs

@[expose] public section

/-!
# Dangling exception addresses: classification (proofs)

Handler resolution of a dangling exception on both sides: `Catches` (native) by induction on the
clauses; Core one step by `Step.handler_inv` and the exit forms of `throwing a`
(`handlerExit_throwing`), then whole handler runs by induction on the clauses.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingExn

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Cfg.Region (Catches)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {a : Nat}

theorem exns_none (hd : Dangling s a) : s.exns[a]? = none :=
  List.getElem?_eq_none hd

/-! ## Clauses -/

theorem catchMatches_iff (hd : Dangling s a) {c : Catch} :
    CatchMatches s f a c ↔ c.CatchesAll := by
  cases c with
  | catch_ x l | catchRef x l =>
    simp only [CatchMatches, Catch.CatchesAll, iff_false]
    rintro ⟨e, -, he, -⟩
    rw [exns_none hd] at he
    cases he
  | catchAll l | catchAllRef l => exact iff_of_true trivial trivial

theorem catches_danglingCatch (hd : Dangling s a) :
    ∀ cs : List Catch, Catches s f a cs (danglingCatch a cs)
  | [] => .empty
  | .catch_ _ _ :: cs =>
    .next (fun h => (catchMatches_iff hd).1 h) (catches_danglingCatch hd cs)
  | .catchRef _ _ :: cs =>
    .next (fun h => (catchMatches_iff hd).1 h) (catches_danglingCatch hd cs)
  | .catchAll _ :: _ => .catchAll
  | .catchAllRef _ :: _ => .catchAllRef

theorem catches_iff (hd : Dangling s a) {cs : List Catch} {r : Option (List Val × LabelIdx)} :
    Catches s f a cs r ↔ r = danglingCatch a cs :=
  ⟨fun h => Region.catches_unique h (catches_danglingCatch hd cs),
    fun h => h ▸ catches_danglingCatch hd cs⟩

/-! ## Exit forms of `throwing a` -/

theorem toAdmin_ne_throwRef (v : Val) : v.toAdmin ≠ .plain .throwRef := by
  rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem throwing_inj {b : Nat} (h : throwing a = throwing b) : a = b := by
  simpa [throwing] using h

/-- `vals vs ++ x :: rest = throwing a` forces `x` to be `ref.exn a` (no values) or `throw_ref`. -/
theorem vals_cons_eq_throwing {vs : List Val} {x : Admin} {rest : List Admin}
    (h : vals vs ++ x :: rest = throwing a) :
    (vs = [] ∧ x = .ref (.exn a)) ∨ (x = .plain .throwRef) := by
  rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
  · simp [vals, throwing] at h; exact .inl ⟨rfl, h.1⟩
  · simp [vals, throwing] at h; exact .inr h.2.1
  · simp [vals, throwing] at h

/-- The exit rules of a handler around `throwing a`: the `throw_ref-handler-*` rules. -/
theorem handlerExit_throwing {n : Nat} {cs : List Catch} {out : List Admin}
    (h : HandlerExit s f n cs (throwing a) out) :
    (cs = [] ∧ out = throwing a) ∨
    (∃ x l cs' e, cs = .catch_ x l :: cs' ∧ s.exns[a]? = some e ∧
      f.module.tags[x.toNat]? = some e.tag ∧ out = vals e.fields ++ [.plain (.br l)]) ∨
    (∃ x l cs' e, cs = .catchRef x l :: cs' ∧ s.exns[a]? = some e ∧
      f.module.tags[x.toNat]? = some e.tag ∧
      out = vals e.fields ++ [.ref (.exn a), .plain (.br l)]) ∨
    (∃ l cs', cs = .catchAll l :: cs' ∧ out = [.plain (.br l)]) ∨
    (∃ l cs', cs = .catchAllRef l :: cs' ∧ out = [.ref (.exn a), .plain (.br l)]) ∨
    (∃ c cs', cs = c :: cs' ∧ ¬ CatchMatches s f a c ∧ out = [.handler n cs' (throwing a)]) := by
  generalize hk : throwing a = k at h
  cases h with
  | vals vs =>
    exfalso
    rcases vs with _ | ⟨v, vs⟩
    · simp [vals, throwing] at hk
    · rcases vals_cons_eq_throwing (vs := []) (x := v.toAdmin) (rest := vals vs) hk.symm with
        ⟨-, h⟩ | h
      · rcases vs with _ | ⟨w, vs⟩
        · simp [vals, throwing] at hk
        · simp [vals, throwing] at hk; exact toAdmin_ne_throwRef w hk.2.1.symm
      · exact toAdmin_ne_throwRef v h
  | br =>
    exfalso
    rcases vals_cons_eq_throwing (by simpa using hk.symm) with ⟨-, h⟩ | h <;> cases h
  | ret =>
    exfalso
    rcases vals_cons_eq_throwing (by simpa using hk.symm) with ⟨-, h⟩ | h <;> cases h
  | returnCall hc =>
    exfalso
    rcases vals_cons_eq_throwing (by simpa using hk.symm) with ⟨-, h⟩ | h <;> (subst h; exact hc)
  | trap => simp [throwing] at hk
  | throwEmpty b => cases throwing_inj hk; exact .inl ⟨rfl, rfl⟩
  | catch_ he ht => cases throwing_inj hk; exact .inr (.inl ⟨_, _, _, _, rfl, he, ht, rfl⟩)
  | catchRef he ht =>
    cases throwing_inj hk; exact .inr (.inr (.inl ⟨_, _, _, _, rfl, he, ht, rfl⟩))
  | catchAll b => cases throwing_inj hk; exact .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))
  | catchAllRef b =>
    cases throwing_inj hk; exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩))))
  | next hn =>
    cases throwing_inj hk; exact .inr (.inr (.inr (.inr (.inr ⟨_, _, rfl, hn, rfl⟩))))

/-! ## Core: one step -/

theorem step_handler_iff (hd : Dangling s a) {n : Nat} {c : Catch} {cs : List Catch}
    {c' : Config H} :
    Step P host ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ c' ↔
      c' = ⟨s, f, danglingNext n a cs c⟩ := by
  constructor
  · intro h
    rcases Step.handler_inv h with ⟨_, _, _, hi, -⟩ | ⟨out, hx, rfl⟩
    · exact absurd hi Step.throwing_stuck
    rcases handlerExit_throwing hx with ⟨h, -⟩ | ⟨x, l, cs', e, -, he, -⟩ |
      ⟨x, l, cs', e, -, he, -⟩ | ⟨l, cs', hc, rfl⟩ | ⟨l, cs', hc, rfl⟩ | ⟨c₀, cs', hc, hn, rfl⟩
    · cases h
    · rw [exns_none hd] at he; cases he
    · rw [exns_none hd] at he; cases he
    · cases hc; rfl
    · cases hc; rfl
    · cases hc
      cases c with
      | catch_ | catchRef => rfl
      | catchAll | catchAllRef => exact absurd trivial hn
  · rintro rfl
    cases c with
    | catch_ x l => exact .throwRefHandlerNext fun h => (catchMatches_iff hd).1 h
    | catchRef x l => exact .throwRefHandlerNext fun h => (catchMatches_iff hd).1 h
    | catchAll l => exact .throwRefHandlerCatchAll
    | catchAllRef l => exact .throwRefHandlerCatchAllRef

theorem step_handler_nil_iff {n : Nat} {c' : Config H} :
    Step P host ⟨s, f, [.handler n [] (throwing a)]⟩ c' ↔ c' = ⟨s, f, throwing a⟩ := by
  constructor
  · intro h
    rcases Step.handler_inv h with ⟨_, _, _, hi, -⟩ | ⟨out, hx, rfl⟩
    · exact absurd hi Step.throwing_stuck
    rcases handlerExit_throwing hx with ⟨-, rfl⟩ | ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩ |
      ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩
    · rfl
    all_goals cases h
  · rintro rfl
    exact .throwRefHandlerEmpty

/-! ## Core: the handler run -/

theorem handlerOut_stuck (r : Option (List Val × LabelIdx)) {c : Config H} :
    ¬ Step P host ⟨s, f, handlerOut a r⟩ c := by
  rcases r with _ | ⟨us, l⟩
  · exact Step.throwing_stuck
  · exact Step.br_vals_stuck

theorem steps_handler (hd : Dangling s a) (n : Nat) (cs : List Catch) :
    Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩
      ⟨s, f, handlerOut a (danglingCatch a cs)⟩ := by
  rcases h : danglingCatch a cs with _ | ⟨us, l⟩
  · exact Region.catches_steps_none (h ▸ catches_danglingCatch hd cs)
  · exact Region.catches_steps (h ▸ catches_danglingCatch hd cs)

theorem steps_cases_head {c₁ c₂ : Config H} (h : Steps P host c₁ c₂) :
    c₁ = c₂ ∨ ∃ c, Step P host c₁ c ∧ Steps P host c c₂ :=
  Relation.ReflTransGen.cases_head h

/-- Every Core run of a handler around a dangling exception that ends in a configuration with no
step ends in `handlerOut a (danglingCatch a cs)`. -/
theorem handler_final (hd : Dangling s a) (n : Nat) :
    ∀ (cs : List Catch) {c' : Config H},
      Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩ c' → (∀ c'', ¬ Step P host c' c'') →
        c' = ⟨s, f, handlerOut a (danglingCatch a cs)⟩
  | [], c', h, hst => by
    rcases steps_cases_head h with rfl | ⟨c, hc, hr⟩
    · exact absurd (step_handler_nil_iff.2 rfl) (hst _)
    · cases step_handler_nil_iff.1 hc
      rcases steps_cases_head hr with rfl | ⟨c₂, h₂, -⟩
      · rfl
      · exact absurd h₂ Step.throwing_stuck
  | c :: cs, c', h, hst => by
    rcases steps_cases_head h with rfl | ⟨c₁, hc, hr⟩
    · exact absurd ((step_handler_iff hd).2 rfl) (hst _)
    cases (step_handler_iff hd).1 hc
    cases c with
    | catch_ x l => exact handler_final hd n cs hr hst
    | catchRef x l => exact handler_final hd n cs hr hst
    | catchAll l =>
      rcases steps_cases_head hr with rfl | ⟨c₂, h₂, -⟩
      · rfl
      · exact absurd h₂ Step.br_stuck
    | catchAllRef l =>
      rcases steps_cases_head hr with rfl | ⟨c₂, h₂, -⟩
      · rfl
      · exact absurd h₂ (Step.br_vals_stuck (us := [.ref (.exn a)]))

/-! ## References -/

theorem not_refOk_exn (hd : Dangling s a) {rt : CRefType} : ¬ RefOk s (.exn a) rt := by
  intro h
  generalize hr : Ref.exn a = r at h
  induction h with
  | exn he => cases hr; rw [exns_none hd] at he; cases he
  | sub _ _ _ ih => exact ih hr
  | _ => cases hr

theorem not_valOk_exn (hd : Dangling s a) {t : CValType} : ¬ ValOk s (.ref (.exn a)) t := by
  intro h
  cases h with
  | ref h => exact not_refOk_exn hd h

theorem not_resultTyped_throw (hd : Dangling s a) {ts : List CValType} :
    ¬ ResultTyped s (.throw a) ts := by
  rintro ⟨e, he⟩
  rw [exns_none hd] at he
  cases he

theorem not_storeOk_of_global (hd : Dangling s a) {gi : GlobalInst} (hg : gi ∈ s.globals)
    (hv : gi.value = .ref (.exn a)) : ¬ StoreOk s := by
  intro hs
  obtain ⟨-, hval⟩ := hs.globals gi hg
  rw [hv] at hval
  exact not_valOk_exn hd hval

end Silmaril.Wasm.Cfg.Proofs.DanglingExn

namespace Silmaril.Wasm.Cfg.Proofs.DanglingExn

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Cfg.Region (Catches)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {a : Nat}

/-! ## Uses of a dangling reference -/

theorem steps_throwRef (ws : List Val) :
    Steps P host ⟨s, f, vals ws ++ throwing a⟩ ⟨s, f, throwing a⟩ := by
  rcases ws with _ | ⟨w, ws⟩
  · exact .refl
  · exact .single (by simpa using Step.throwRefInstrs (rest := []) (Or.inl (List.cons_ne_nil w ws)))

/-! ## The native handler of `try_table` -/

theorem evalLXPh_try {s₀ : Store H} {f₀ f₁ : Frame} {stk : List Val} {bt : BlockType}
    {cs : List Catch} {body es : List Binaryen.BExpr} {np nr : Nat} {l : List (Abstract.OCall H)}
    (har : Binaryen.arity f₀ bt = some (np, nr))
    (hbody : Abstract.EvalLXPh s₀ f₀ (stk.take np) body l (s, f₁, .flow (.throw a)))
    (hd : Dangling s a) :
    Abstract.EvalLXPh s₀ f₀ stk (.tryTable bt cs body :: es) l
      (match danglingCatch a cs with
        | some (us, l') => (s, f₁, .flow (.brk l'.toNat (us.reverse ++ stk.drop np)))
        | none => (s, f₁, .flow (.throw a))) := by
  rcases h : danglingCatch a cs with _ | ⟨us, l'⟩
  · exact .tryRethrow har hbody ((catches_iff hd).2 h.symm)
  · exact .tryCatch har hbody ((catches_iff hd).2 h.symm)

end Silmaril.Wasm.Cfg.Proofs.DanglingExn
