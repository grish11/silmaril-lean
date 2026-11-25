module

public import Silmaril.SSA.RVSDG.LambdaSSA.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Defs

/-! # A scoped terminal switch

A λSSA case spine matches a multiway γ whose arms each return one of the
explicitly passed payload ports. The input selector is separate from the
payload. The unit and suffix binders created by λSSA case analysis only
participate in dispatch.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open Silmaril.Isotope.LambdaSSA (Tm)

universe u v
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {Γ : List τ} {A : τ}

/-- Left-first case spine. The final singleton tag requires no further case. -/
def switch : (n : Nat) → {Γ : List τ} → Port Γ (selectorType n) →
    (Fin (n + 1) → Port Γ A) → Tm Φ
  | 0, _, _, arms => .var (index (arms 0))
  | n + 1, _, selector, arms => .case (.var (index selector))
      (.var (index (.tail (arms 0) : Port (unit :: _) A)))
      (switch n .head (fun i => .tail (arms i.succ)))

/-- Assemble a vector of wires by visiting all typed destination ports in order. -/
def wiresOf {args : Ports (Ty τ)} {past : List (Ports (Ty τ))} :
    (ports : Ports (Ty τ)) → (∀ {t : Ty τ}, Port ports t → Origin args past t) →
    Wires args past ports
  | [], _ => .nil
  | _ :: tail, wire => .cons (wire .head) (wiresOf tail fun p => wire (.tail p))

/-- A single root γ with selector followed by the captured payload. Each
child sees only the payload and directly reads its selected result port. -/
def gammaTerm (extra : Nat) (arms : Fin (extra + 2) → Port Γ A) :
    Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A] :=
  let node : Node (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [.value A] :=
    ⟨.control (extra + 2) :: inputs Γ, .gamma extra, wiresOf _ Origin.arg, fun _ => []⟩
  .bind node (fun i => .ret (.cons (.arg (inputPort (arms i))) .nil))
    (.ret (.cons (.output ⟨0, Nat.zero_lt_succ _⟩ .head) .nil))

/-- Syntax-directed relation for the terminal γ slice. The same arm-indexed
payload positions generate the case spine and the γ child result edges. -/
inductive GammaRelated (extra : Nat) : Tm Φ →
    Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A] → Type (max u v) where
  | intro (arms : Fin (extra + 2) → Port Γ A) :
      GammaRelated extra (switch (extra + 1) .head (fun i => .tail (arms i))) (gammaTerm extra arms)

/-- Exact syntactic admission at the λSSA end of the terminal switch. -/
abbrev GammaSSAForm (extra : Nat) (t : Tm Φ) (Γ : List τ) (A : τ) :=
  {arms : Fin (extra + 2) → Port Γ A //
    switch (extra + 1) .head (fun i => .tail (arms i)) = t}

/-- Exact syntactic admission at the RVSDG end of the terminal switch. -/
abbrev GammaRVForm (extra : Nat)
    (rv : Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A]) :=
  {arms : Fin (extra + 2) → Port Γ A // gammaTerm extra arms = rv}

def lowerGamma {extra : Nat} {t : Tm Φ} (h : GammaSSAForm extra t Γ A) :
    Σ rv : Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A],
      GammaRelated extra t rv :=
  let ⟨arms, eq⟩ := h
  ⟨gammaTerm extra arms, Eq.mp (congrArg (fun x => GammaRelated extra x (gammaTerm extra arms)) eq)
    (GammaRelated.intro arms)⟩

def raiseGamma {extra : Nat}
    {rv : Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A]}
    (h : GammaRVForm extra rv) : Σ t : Tm Φ, GammaRelated extra t rv :=
  let ⟨arms, eq⟩ := h
  let t : Tm Φ := switch (extra + 1) .head (fun i => .tail (arms i))
  ⟨t, Eq.mp (congrArg (GammaRelated extra t) eq) (GammaRelated.intro arms)⟩

end Silmaril.SSA.RVSDG.LambdaSSA
