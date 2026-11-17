module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Approx

@[expose] public section

/-!
# Redirecting exception addresses (proofs)

`scrubR N r` replaces every exception address of `r` (also under `extern`) by `N`. A typed
reference stays typed when `N` is an exception (`refOk_scrub`), and it is equal to its
redirection up to exception addresses (`refApprox_scrub`). `ChainTo a r`: `r` is `ref.exn a`
under some `extern` wrappers. A redirected reference is unchanged or a chain to `N`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- Redirect every exception address of a reference to `N`. -/
def scrubR (N : Nat) : Ref → Ref
  | .exn _ => .exn N
  | .extern r => .extern (scrubR N r)
  | r => r

/-- Redirect every exception address of a value to `N`. -/
def scrubV (N : Nat) : Val → Val
  | .ref r => .ref (scrubR N r)
  | v => v

/-- Redirect the exception addresses of the fields of an exception to `N`. -/
def scrubE (N : Nat) (e : ExnInst) : ExnInst := ⟨e.tag, e.fields.map (scrubV N)⟩

/-- Every exception address of a reference satisfies `p`. -/
def RefLeaves (p : Nat → Prop) : Ref → Prop
  | .exn a => p a
  | .extern r => RefLeaves p r
  | _ => True

/-- `r` is `ref.exn a` under `extern` wrappers. -/
def ChainTo (a : Nat) : Ref → Prop
  | .exn b => b = a
  | .extern r => ChainTo a r
  | _ => False

theorem scrubR_ne_null {N : Nat} {r : Ref} (h : r ≠ .null) : scrubR N r ≠ .null := by
  cases r <;> simp_all [scrubR]

theorem refOk_scrub {s : Store H} {N : Nat} {e : ExnInst} (hN : s.exns[N]? = some e) {r : Ref}
    {rt : CRefType} (h : RefOk s r rt) : RefOk s (scrubR N r) rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h => exact .func h
  | exn _ => exact .exn hN
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih (scrubR_ne_null hn)
  | sub _ hok hs ih => exact .sub ih hok hs

theorem valOk_scrub {s : Store H} {N : Nat} {e : ExnInst} (hN : s.exns[N]? = some e) {v : Val}
    {t : CValType} (h : ValOk s v t) : ValOk s (scrubV N v) t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (refOk_scrub hN h)

theorem refLeaves_of_refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    RefLeaves (· < s.exns.length) r := by
  induction h with
  | exn h => exact (List.getElem?_eq_some_iff.1 h).1
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

theorem refApprox_scrub_self {M N : Nat} : ∀ {r : Ref}, RefLeaves (· < M) r →
    RefApprox M r (scrubR N r)
  | .exn _, h => .exn h
  | .extern r, h => .extern (refApprox_scrub_self (r := r) h)
  | .null, _ => .refl _
  | .i31 _, _ => .refl _
  | .struct _, _ => .refl _
  | .array _, _ => .refl _
  | .func _, _ => .refl _
  | .host _, _ => .refl _

theorem refApprox_scrub {M N : Nat} {r r' : Ref} (h : RefApprox M r r')
    (hl : RefLeaves (· < M) r') : RefApprox M r (scrubR N r') := by
  induction h with
  | refl r => exact refApprox_scrub_self hl
  | exn ha => exact .exn ha
  | extern _ ih => exact .extern (ih hl)

theorem valApprox_scrub {M N : Nat} {v w : Val} (h : ValApprox M v w)
    (hl : ∀ r, w = .ref r → RefLeaves (· < M) r) : ValApprox M v (scrubV N w) := by
  rcases h with rfl | ⟨r, r', rfl, rfl, hr⟩
  · cases v with
    | ref r => exact .inr ⟨r, _, rfl, rfl, refApprox_scrub_self (hl r rfl)⟩
    | _ => exact .inl rfl
  · exact .inr ⟨r, _, rfl, rfl, refApprox_scrub hr (hl r' rfl)⟩

theorem scrubR_cases (N : Nat) : ∀ r : Ref, scrubR N r = r ∨ ChainTo N (scrubR N r)
  | .exn _ => .inr rfl
  | .extern r => by
    rcases scrubR_cases N r with h | h
    · exact .inl (by simp [scrubR, h])
    · exact .inr h
  | .null => .inl rfl
  | .i31 _ => .inl rfl
  | .struct _ => .inl rfl
  | .array _ => .inl rfl
  | .func _ => .inl rfl
  | .host _ => .inl rfl

theorem chainTo_scrubR {a N : Nat} : ∀ {r : Ref}, ChainTo a (scrubR N r) → a = N
  | .exn _, h => h.symm
  | .extern r, h => chainTo_scrubR (r := r) h
  | .null, h => h.elim
  | .i31 _, h => h.elim
  | .struct _, h => h.elim
  | .array _, h => h.elim
  | .func _, h => h.elim
  | .host _, h => h.elim

theorem not_chainTo_of_leaves {a : Nat} : ∀ {r : Ref}, RefLeaves (· < a) r → ¬ ChainTo a r
  | .exn _, h, h' => by simp only [RefLeaves, ChainTo] at h h'; omega
  | .extern r, h, h' => not_chainTo_of_leaves (r := r) h h'
  | .null, _, h' => h'
  | .i31 _, _, h' => h'
  | .struct _, _, h' => h'
  | .array _, _, h' => h'
  | .func _, _, h' => h'
  | .host _, _, h' => h'

theorem RefLeaves.mono {p q : Nat → Prop} (hpq : ∀ a, p a → q a) :
    ∀ {r : Ref}, RefLeaves p r → RefLeaves q r
  | .exn a, h => hpq a h
  | .extern r, h => RefLeaves.mono hpq (r := r) h
  | .null, _ => trivial
  | .i31 _, _ => trivial
  | .struct _, _ => trivial
  | .array _, _ => trivial
  | .func _, _ => trivial
  | .host _, _ => trivial

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
