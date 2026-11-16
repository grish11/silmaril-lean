module

public import Silmaril.Logic.Kore.Modules.Semantics.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Semantics
open Silmaril.Logic.Kore Silmaril.Logic.Kore.Modules
open Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Silmaril.Logic.Matching.FirstOrder.Model scope.signature)

/-- Binder shadowing corresponds to extending the direct environment; existing
alias arguments retain exactly their denotations under weakening. -/
theorem interpret_bind {k : Nat} {Γ : Fin k → String}
    (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) (name b : String) (x : M.carrier b) :
    interpret M (Checking.bind name b vs) (Fin.cases x v) =
      ⟨name, b, {x}⟩ :: interpret M vs v := by
  simp only [interpret, Checking.bind, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry _
  simp only [Function.comp_apply, Checking.weakenBinding, Checking.denote_weaken]

theorem lookup_correct {k : Nat} {Γ : Fin k → String}
    (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) (name s : String)
    (p : FirstOrder.Pattern scope.signature Γ s)
    (h : Checking.lookupVariable vs name s = some p) :
    lookup M (interpret M vs v) name s = FirstOrder.denote scope.signature M v p := by
  induction vs with
  | nil => simp [Checking.lookupVariable] at h
  | cons entry rest ih =>
      rcases entry with ⟨n, t, q⟩
      by_cases hn : (n == name) = true
      · simp only [Checking.lookupVariable, List.find?_cons, hn] at h
        change (if hs : t = s then some (hs ▸ q) else none) = some p at h
        split at h
        · rename_i hs
          cases hs
          cases h
          simp [lookup, interpret, hn]
        · contradiction
      · simp only [Checking.lookupVariable, List.find?_cons, hn] at h
        simpa only [lookup, interpret, List.map_cons, List.find?_cons, hn, ↓reduceIte]
          using ih h

/-- Successful dependent collection retains every original elaboration result. -/
theorem collect_some {n : Nat} {α : Fin n → Type}
    (f : (i : Fin n) → Option (α i)) (xs : (i : Fin n) → α i)
    (h : Checking.collect f = some xs) : ∀ i, f i = some (xs i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      cases hhead : f 0 with
      | none => simp [Checking.collect, hhead] at h
      | some head =>
          cases htail : Checking.collect (fun i => f i.succ) with
          | none => simp [Checking.collect, hhead, htail] at h
          | some tail =>
              simp only [Checking.collect, hhead, htail] at h
              cases h
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact hhead
              · exact ih _ _ htail j

/-- A successful finite argument traversal can be interpreted pointwise. -/
theorem mapM_interpret {α β γ : Type} (xs : List α) (f : α → Option β)
    (g : α → γ) (eval : β → γ) (ys : List β)
    (h : xs.mapM f = some ys)
    (ok : ∀ a b, f a = some b → eval b = g a) : ys.map eval = xs.map g := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; rfl
  | cons a rest ih =>
      cases ha : f a with
      | none => simp [ha] at h
      | some b =>
          cases hr : rest.mapM f with
          | none => simp [ha, hr] at h
          | some tail =>
              simp only [List.mapM_cons, ha, hr] at h
              cases h
              exact congrArg₂ List.cons (ok a b ha) (ih tail hr)
end Silmaril.Proofs.Logic.Kore.Modules.Semantics
