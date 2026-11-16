module

public import Silmaril.Logic.Matching.GuardedLFP.Defs
public import Silmaril.Logic.Matching.GuardedLFP.Binders

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples

abbrev objSort {S : FOL.Signature} (s : S.S) : MatchingSort S := .base (.object s)
abbrev objContext {S : FOL.Signature} {k : Nat} (Γ : Fin k → S.S) := objSort ∘ Γ
abbrev setContext {S : FOL.Signature} {r : Nat} (P : Fin r → Profile S) := MatchingSort.tuple ∘ P

abbrev term {S : FOL.Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {s : S.S} (t : EQ.Term S.toSignature Γ s) :
    FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Γ) (objSort s) :=
  .base ((baseSignature S).pattern (GuardedFOL.term t))

abbrev tupleDefined {S : FOL.Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → MatchingSort S} {p : Profile S}
    (t : FixedPoint.Pattern (signature S).symbols (setContext P) Γ (.tuple p)) :
    FixedPoint.Pattern (signature S).symbols (setContext P) Γ (.base .truth) :=
  .app (.defined p) (fun _ => t)

abbrev packTerms {S : FOL.Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {p : Profile S} (args : ∀ j, EQ.Term S.toSignature Γ (p.sorts j)) :
    FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Γ) (.tuple p) :=
  .app (.pack p) (fun j => term (args j))

def prefixVar {S : FOL.Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (p : Profile S) (j : Fin p.arity) :
    FixedPoint.Pattern (signature S).symbols (setContext P)
      (blockContext (objContext Γ) (objContext p.sorts)) (objSort (p.sorts j)) :=
  Eq.mp (congrArg (fun s => FixedPoint.Pattern (signature S).symbols (setContext P)
    (blockContext (objContext Γ) (objContext p.sorts)) s)
    (blockContext_prefix (objContext Γ) (objContext p.sorts) j)) (.base (.var (prefixIndex j)))

abbrev prefixPack {S : FOL.Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (p : Profile S) :
    FixedPoint.Pattern (signature S).symbols (setContext P)
      (blockContext (objContext Γ) (objContext p.sorts)) (.tuple p) :=
  .app (.pack p) (fun j => prefixVar p j)

theorem context_extend {S : FOL.Signature} {k : Nat} (Δ : Fin (k+1) → S.S) :
    objContext Δ = Fin.cases (objSort (Δ 0)) (objContext (Δ ∘ Fin.succ)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def tupleBody {S : FOL.Signature} {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FixedPoint.Pattern (signature S).symbols (setContext P') (objContext Δ) (.base .truth)) :
    FixedPoint.Pattern (signature S).symbols (setContext P') (objContext Γ) (.tuple (P' 0)) :=
  bindPrefix (.conj (prefixPack (Γ := Γ) (P' 0))
    (.app (.liftTruth (P' 0)) (fun _ => body.renameObjects
      (blockRen (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp)))))

/-- Positive source recursion becomes native tuple-valued μ. The recursive body
binds precisely the tuple prefix; Γ remains the captured parameter context. -/
def formula {S : FOL.Signature} : {r k : Nat} → {P : Fin r → Profile S} →
    {Γ : Fin k → S.S} → FirstOrderLFP.Formula S P Γ →
    FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Γ) (.base .truth)
  | _, _, _, _, .base p => .base ((baseSignature S).pattern (GuardedFOL.formula p))
  | _, _, _, _, .pred i args => tupleDefined (.conj (packTerms args) (.setvar i))
  | _, _, _, _, .conj p q => .conj (formula p) (formula q)
  | _, _, _, _, .disj p q => .disj (formula p) (formula q)
  | _, _, _, _, @FirstOrderLFP.Formula.all _ _ _ _ Δ p =>
      .all (objSort (Δ 0)) ((context_extend Δ) ▸
        .disj (.base ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ)))) (formula p))
  | _, _, _, _, @FirstOrderLFP.Formula.ex _ _ _ _ Δ p =>
      .ex (objSort (Δ 0)) ((context_extend Δ) ▸
        .conj (.base ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))) (formula p))
  | _, _, _, _Γ, @FirstOrderLFP.Formula.lfp _ _ _ P' _ _Δ ht hp body args =>
      tupleDefined (.conj (packTerms args) (.mu (tupleBody ht hp (formula body))))
end Silmaril.Logic.Matching.GuardedLFP
