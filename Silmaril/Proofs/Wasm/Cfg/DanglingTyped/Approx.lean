module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-!
# Code equal up to exception references (proofs)

`CodeApprox N es es'`: `es` (actual code) and `es'` (witness code) agree except that an exception
reference `ref.exn a` of `es` with `a < N` may be any exception reference `ref.exn b` in `es'`,
inside labels, handlers and frames too. `AdminsOk` only checks that an exception reference names
an exception, so typing of `es'` in a store with `N` exceptions types `es` (`adminsOk_approx`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- Values equal up to exception references (the left one below `N`). -/
def ValApprox (N : Nat) (v w : Val) : Prop :=
  v = w ∨ ∃ a b, v = .ref (.exn a) ∧ w = .ref (.exn b) ∧ a < N

mutual

/-- Administrative instructions equal up to exception references. -/
inductive AdminApprox (N : Nat) : Admin → Admin → Prop where
  | refl (a : Admin) : AdminApprox N a a
  | exn {a b : Nat} (h : a < N) : AdminApprox N (.ref (.exn a)) (.ref (.exn b))
  | label (n : Nat) (cont : List Instr) {b b' : List Admin} (h : CodeApprox N b b') :
      AdminApprox N (.label n cont b) (.label n cont b')
  | handler (n : Nat) (cs : List Catch) {b b' : List Admin} (h : CodeApprox N b b') :
      AdminApprox N (.handler n cs b) (.handler n cs b')
  | frame (n : Nat) (fr : Frame) {b b' : List Admin} (h : CodeApprox N b b') :
      AdminApprox N (.frame n fr b) (.frame n fr b')

/-- Code equal up to exception references. -/
inductive CodeApprox (N : Nat) : List Admin → List Admin → Prop where
  | nil : CodeApprox N [] []
  | cons {a a' : Admin} {es es' : List Admin} (ha : AdminApprox N a a')
      (hs : CodeApprox N es es') : CodeApprox N (a :: es) (a' :: es')

end

namespace CodeApprox

variable {N : Nat}

theorem refl : ∀ es : List Admin, CodeApprox N es es
  | [] => .nil
  | a :: es => .cons (.refl a) (refl es)

theorem append : ∀ {es es' fs fs' : List Admin}, CodeApprox N es es' → CodeApprox N fs fs' →
    CodeApprox N (es ++ fs) (es' ++ fs')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hs, h => .cons ha (append hs h)

theorem append_inv : ∀ {es : List Admin} {l₁ l₂ : List Admin}, CodeApprox N es (l₁ ++ l₂) →
    ∃ e₁ e₂, es = e₁ ++ e₂ ∧ CodeApprox N e₁ l₁ ∧ CodeApprox N e₂ l₂
  | es, [], l₂, h => ⟨[], es, rfl, .nil, h⟩
  | _, a :: l₁, l₂, .cons ha hs => by
    obtain ⟨e₁, e₂, rfl, h₁, h₂⟩ := append_inv hs
    exact ⟨_ :: e₁, e₂, rfl, .cons ha h₁, h₂⟩

theorem cons_inv {es : List Admin} {a : Admin} {l : List Admin} (h : CodeApprox N es (a :: l)) :
    ∃ a₀ es₀, es = a₀ :: es₀ ∧ AdminApprox N a₀ a ∧ CodeApprox N es₀ l := by
  cases h with
  | cons ha hs => exact ⟨_, _, rfl, ha, hs⟩

theorem nil_inv {es : List Admin} (h : CodeApprox N es []) : es = [] := by
  cases h; rfl

theorem of_vals : ∀ {vs ws : List Val}, List.Forall₂ (ValApprox N) vs ws →
    CodeApprox N (vals vs) (vals ws)
  | _, _, .nil => .nil
  | _, _, .cons h hs => by
    refine .cons ?_ (of_vals hs)
    rcases h with rfl | ⟨a, b, rfl, rfl, ha⟩
    · exact .refl _
    · exact .exn ha

end CodeApprox

/-- An exception reference of an existing exception has every type another one has. -/
theorem refOk_exn_retarget {s : Store H} {a b : Nat} {rt : CRefType} {e : ExnInst}
    (he : s.exns[a]? = some e) (h : RefOk s (.exn b) rt) : RefOk s (.exn a) rt := by
  generalize hr : Ref.exn b = r at h
  induction h with
  | exn _ => exact .exn he
  | sub _ hok hs ih => exact .sub (ih hr) hok hs
  | _ => cases hr

theorem valOk_approx {s : Store H} {v w : Val} {t : CValType} (hv : ValApprox s.exns.length v w)
    (h : ValOk s w t) : ValOk s v t := by
  rcases hv with rfl | ⟨a, b, rfl, rfl, ha⟩
  · exact h
  · cases h with
    | ref h => exact .ref (refOk_exn_retarget (List.getElem?_eq_getElem ha) h)

mutual

theorem adminOk_approx {s : Store H} :
    ∀ {C : Context} {a a₀ : Admin} {it : InstrType}, AdminOk s C a it →
      AdminApprox s.exns.length a₀ a → AdminOk s C a₀ it
  | _, _, _, _, h, .refl _ => h
  | _, _, _, _, .ref h, .exn ha => .ref (refOk_exn_retarget (List.getElem?_eq_getElem ha) h)
  | _, _, _, _, .label hn hc hb, .label _ _ hx => .label hn hc (adminsOk_approx hb hx)
  | _, _, _, _, .frame hf hn hb hok, .frame _ _ hx => .frame hf hn (adminsOk_approx hb hx) hok
  | _, _, _, _, .handler hc hb, .handler _ _ hx => .handler hc (adminsOk_approx hb hx)

theorem adminsOk_approx {s : Store H} :
    ∀ {C : Context} {as as₀ : List Admin} {it : InstrType}, AdminsOk s C as it →
      CodeApprox s.exns.length as₀ as → AdminsOk s C as₀ it
  | _, _, _, _, .nil, hx => by rw [hx.nil_inv]; exact .nil
  | _, _, _, _, .single h, hx => by
    obtain ⟨a₀, es₀, rfl, ha, hs⟩ := hx.cons_inv
    rw [hs.nil_inv]
    exact .single (adminOk_approx h ha)
  | _, _, _, _, .seq h₁ hl h₂, hx => by
    obtain ⟨e₁, e₂, rfl, x₁, x₂⟩ := hx.append_inv
    exact .seq (adminsOk_approx h₁ x₁) hl (adminsOk_approx h₂ x₂)
  | _, _, _, _, .cons ha hl hs, hx => by
    obtain ⟨a₀, es₀, rfl, x₁, x₂⟩ := hx.cons_inv
    exact .cons (adminOk_approx ha x₁) hl (adminsOk_approx hs x₂)
  | _, _, _, _, .sub h hsub hok, hx => .sub (adminsOk_approx h hx) hsub hok
  | _, _, _, _, .frame h hok, hx => .frame (adminsOk_approx h hx) hok

end

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
