module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Structural.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Extend a target assignment beneath a shared innermost binder. -/
def lift {n k : ℕ} (σ : Fin n → ETm k) : Fin (n + 1) → ETm (k + 1) :=
  Fin.cons (.bv 0) (fun i => (σ i).wk0)

/-- Translate all scoped constructors, currying Nat steps and erasing based J. -/
def term {n k : ℕ} (σ : Fin n → ETm k) : Term n → ETm k
  | .var i => σ i
  | .univ i => .univ i
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nat => .nats
  | .zero => .zero
  | .succ t => .succ (term σ t)
  | .pi A B => .pi (term σ A) (term (lift σ) B)
  | .sigma A B => .sigma (term σ A) (term (lift σ) B)
  | .lam A b => .abs (term σ A) (term (lift σ) b)
  | .app f a => .app (term σ f) (term σ a)
  | .pair a b => .pair (term σ a) (term σ b)
  | .fst p => .fst (term σ p)
  | .snd p => .snd (term σ p)
  | .natrec C z s t =>
      .natrec (term (lift σ) C) (.app (term σ s).wk0 (.bv 0)) (term σ z) (term σ t)
  | .absurd A e => .absurd (term σ A) (term σ e)
  | .id A a b => .id (term σ A) (term σ a) (term σ b)
  | .refl a => .refl (term σ a)
  | .j _ _ _ d _ _ => term σ d

/-- Interpret every source telescope variable as the corresponding target free name. -/
def named {n : ℕ} (ι : Fin n → String) (t : Term n) : ETm 0 :=
  term (fun i => .fv (ι i)) t

/-- Translate declarations recursively, using each preceding telescope's own names. -/
def context : {n : ℕ} → Context n → (Fin n → String) → ECtx
  | _, .nil, _ => .nil
  | _, .snoc Γ A, ι =>
      (context Γ (fun i => ι i.succ)).cons (ι 0) (named (fun i => ι i.succ) A)

/-- Pairwise distinct canonical names, represented by strings of distinct lengths. -/
def name {n : ℕ} (i : Fin n) : String := String.ofList (List.replicate i.val 'x')


end Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
