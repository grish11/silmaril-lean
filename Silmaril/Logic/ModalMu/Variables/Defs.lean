module

public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu

/-- Lift a free-variable renaming under a binder, preserving its fresh index zero. -/
def liftVars {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

def Formula.renameVars {S : Signature} : {n m : Nat} →
    (Fin n → Fin m) → Formula S n → Formula S m
  | _, _, _, .pos a => .pos a
  | _, _, _, .neg a => .neg a
  | _, _, _, .bot => .bot
  | _, _, _, .top => .top
  | _, _, f, .var i => .var (f i)
  | _, _, f, .conj p q => .conj (p.renameVars f) (q.renameVars f)
  | _, _, f, .disj p q => .disj (p.renameVars f) (q.renameVars f)
  | _, _, f, .box a p => .box a (p.renameVars f)
  | _, _, f, .diamond a p => .diamond a (p.renameVars f)
  | _, _, f, .mu p => .mu (p.renameVars (liftVars f))
  | _, _, f, .nu p => .nu (p.renameVars (liftVars f))

def Formula.shift {S : Signature} {n : Nat} (p : Formula S n) : Formula S (n + 1) :=
  p.renameVars Fin.succ

def Formula.closedAt {S : Signature} (n : Nat) (p : Formula S 0) : Formula S n :=
  p.renameVars Fin.elim0

end Silmaril.Logic.ModalMu
