module

public import Silmaril.Wasi.Component.Consequence.Gentzen.Defs
public import Silmaril.Proofs.Wasi.Component.Consequence.Checkers

/-!
# Gentzen sequents from component checkers: proofs

The clash checker's decoder inverts its encoding (`clashDec_iff`), and clashes are sound for
UNSAT and for TAUTO under signed satisfaction (`clash_unsat`, `clash_taut`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Wasi Silmaril.Wasi.Accept Silmaril.Wasi.Consequence
open Silmaril.Consequence (Signed)
open Silmaril.Wasm.Component (Val)

theorem mapM_eq_some_iff_of_inverse {α : Type} {d : Val → Option α} {e : α → Val}
    (h : ∀ v a, d v = some a ↔ v = e a) (vs : List Val) (xs : List α) :
    vs.mapM d = some xs ↔ vs = xs.map e := by
  induction vs generalizing xs with
  | nil => cases xs <;> simp
  | cons v vs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    constructor
    · rintro ⟨y, hy, ys, hys, rfl⟩
      simp [(h _ _).1 hy, (ih ys).1 hys]
    · intro hv
      cases xs with
      | nil => cases hv
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at hv
        exact ⟨y, (h _ _).2 hv.1, ys, (ih ys).2 hv.2, rfl⟩

theorem signedU32?_iff (v : Val) (a : Signed (BitVec 32)) :
    signedU32? v = some a ↔ v = signedU32 a := by
  constructor
  · intro h
    unfold signedU32? at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  · rintro rfl; cases a <;> rfl

theorem clashDec_iff (args : List Val) (q : Unit × List (Signed (BitVec 32))) :
    (clashDec args).map ((), ·) = some q ↔ args = clashEnc q := by
  obtain ⟨⟨⟩, xs⟩ := q
  rcases args with _ | ⟨a, _ | _⟩ <;>
    simp [clashDec, args1, clashEnc, Option.bind_eq_some_iff, ofRecord?_eq_some,
      mapM_eq_some_iff_of_inverse signedU32?_iff]

theorem signedSat_neg {M A : Type} (v : M → A → Prop) (m : M) (x : Signed A) :
    signedSat v m (-x) ↔ ¬ signedSat v m x := by
  cases x <;> simp [signedSat, Neg.neg, Signed.flip]

theorem clash_unsat {M A : Type} (v : M → A → Prop) (Γ : List (Signed A)) (h : Clash Γ) :
    Silmaril.Consequence.Refutation.Unsat (signedSat v) Γ := by
  obtain ⟨x, hx, hnx⟩ := h
  intro m hm
  exact (signedSat_neg v m x).1 (hm _ hnx) (hm _ hx)

theorem clash_taut {M A : Type} (v : M → A → Prop) (Δ : List (Signed A)) (h : Clash Δ) :
    Silmaril.Consequence.Gentzen.Taut (signedSat v) Δ := by
  obtain ⟨x, hx, hnx⟩ := h
  intro m _
  by_cases hm : signedSat v m x
  · exact ⟨x, hx, hm⟩
  · exact ⟨-x, hnx, (signedSat_neg v m x).2 hm⟩

end Silmaril.Proofs.Wasi.Component.Consequence
