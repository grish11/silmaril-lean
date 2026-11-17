module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-!
# Code equal up to exception references (proofs)

`CodeApprox N es es'`: `es` (actual code) and `es'` (witness code) agree except that an exception
reference `ref.exn a` of `es` with `a < N` may be any exception reference `ref.exn b` in `es'`,
also under `extern` wrappers (`RefApprox`), inside labels, handlers and frames too. `AdminsOk` only checks that an exception reference names
an exception, so typing of `es'` in a store with `N` exceptions types `es` (`adminsOk_approx`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- References equal up to exception addresses (the left ones below `N`). -/
inductive RefApprox (N : Nat) : Ref → Ref → Prop where
  | refl (r : Ref) : RefApprox N r r
  | exn {a b : Nat} (h : a < N) : RefApprox N (.exn a) (.exn b)
  | extern {r r' : Ref} (h : RefApprox N r r') : RefApprox N (.extern r) (.extern r')

/-- Values equal up to exception addresses (the left ones below `N`). -/
def ValApprox (N : Nat) (v w : Val) : Prop :=
  v = w ∨ ∃ r r', v = .ref r ∧ w = .ref r' ∧ RefApprox N r r'

mutual

/-- Administrative instructions equal up to exception references. -/
inductive AdminApprox (N : Nat) : Admin → Admin → Prop where
  | refl (a : Admin) : AdminApprox N a a
  | ref {r r' : Ref} (h : RefApprox N r r') : AdminApprox N (.ref r) (.ref r')
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
    rcases h with rfl | ⟨r, r', rfl, rfl, hr⟩
    · exact .refl _
    · exact .ref hr

end CodeApprox

theorem RefApprox.mono {N M : Nat} (h : N ≤ M) {r r' : Ref} (hr : RefApprox N r r') :
    RefApprox M r r' := by
  induction hr with
  | refl r => exact .refl r
  | exn ha => exact .exn (Nat.lt_of_lt_of_le ha h)
  | extern _ ih => exact .extern ih

theorem ValApprox.mono {N M : Nat} (h : N ≤ M) {v w : Val} (hv : ValApprox N v w) :
    ValApprox M v w := by
  rcases hv with rfl | ⟨r, r', rfl, rfl, hr⟩
  · exact .inl rfl
  · exact .inr ⟨r, r', rfl, rfl, hr.mono h⟩

theorem RefApprox.ne_null {N : Nat} {r r' : Ref} (h : RefApprox N r r') (hn : r' ≠ .null) :
    r ≠ .null := by
  cases h with
  | refl => exact hn
  | exn => exact Ref.noConfusion
  | extern => exact Ref.noConfusion

/-- **A reference equal up to existing exception addresses has the same types.** -/
theorem refOk_approx {s : Store H} {r' : Ref} {rt : CRefType} (h : RefOk s r' rt) :
    ∀ {r : Ref}, RefApprox s.exns.length r r' → RefOk s r rt := by
  induction h with
  | exn _ =>
    intro r hr
    cases hr with
    | refl => exact .exn ‹_›
    | exn ha => exact .exn (List.getElem?_eq_getElem ha)
  | extern _ hn ih =>
    intro r hr
    cases hr with
    | refl => exact .extern (ih (.refl _)) hn
    | extern hr => exact .extern (ih hr) (hr.ne_null hn)
  | sub _ hok hs ih => intro r hr; exact .sub (ih hr) hok hs
  | null => intro r hr; cases hr; exact .null
  | i31 b => intro r hr; cases hr; exact .i31 b
  | struct h => intro r hr; cases hr; exact .struct h
  | array h => intro r hr; cases hr; exact .array h
  | func h => intro r hr; cases hr; exact .func h
  | host a => intro r hr; cases hr; exact .host a

theorem valOk_approx {s : Store H} {v w : Val} {t : CValType} (hv : ValApprox s.exns.length v w)
    (h : ValOk s w t) : ValOk s v t := by
  rcases hv with rfl | ⟨r, r', rfl, rfl, hr⟩
  · exact h
  · cases h with
    | ref h => exact .ref (refOk_approx h hr)

mutual

theorem adminOk_approx {s : Store H} :
    ∀ {C : Context} {a a₀ : Admin} {it : InstrType}, AdminOk s C a it →
      AdminApprox s.exns.length a₀ a → AdminOk s C a₀ it
  | _, _, _, _, h, .refl _ => h
  | _, _, _, _, .ref h, .ref hr => .ref (refOk_approx h hr)
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
