module

public import Silmaril.Courses.Cambridge.L2.Syntax

/-! # Typed lexical environments for the L2 denotations -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Denotation

/-- One semantic value per binder, with the nearest binder first. -/
def LexicalEnv (V : Ty → Type) : List Ty → Type
  | [] => Unit
  | A :: Γ => V A × LexicalEnv V Γ

def LexicalEnv.empty {V : Ty → Type} : LexicalEnv V [] := ()

def LexicalEnv.push {V : Ty → Type} {Γ : List Ty} {A : Ty}
    (environment : LexicalEnv V Γ) (value : V A) : LexicalEnv V (A :: Γ) :=
  (value, environment)

def LexicalEnv.lookup {V : Ty → Type} : {Γ : List Ty} → LexicalEnv V Γ → {i : Nat} → {T : Ty} →
    Γ[i]? = some T → V T
  | [], _, _, _, lookup => by simp at lookup
  | _ :: _, environment, 0, _, lookup => by
    cases Option.some.inj lookup
    exact environment.1
  | _ :: _, environment, _ + 1, _, lookup => LexicalEnv.lookup environment.2 lookup

end Silmaril.Courses.Cambridge.L2.Denotation
