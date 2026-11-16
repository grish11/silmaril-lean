module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Defs
public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion

abbrev SourceTerm := Silmaril.Logic.TypeTheory.IntensionalMLTT.Term

/-- Extend a source-variable assignment beneath a native binder. -/
def lift {n : ℕ} (σ : Fin n → LambdaPi.Term) : Fin (n + 1) → LambdaPi.Term :=
  Fin.cons (.var 0) (fun i => (σ i).rename Nat.succ)

/-- Compile the LF constructors under an explicit assignment of source variables.
The shared MLTT syntax has extra constructors with no LF rules; these are mapped
to a inert placeholder atom. No theorem here interprets those extra constructors. -/
def term {n : ℕ} (σ : Fin n → LambdaPi.Term) : SourceTerm n → LambdaPi.Term
  | .var i => σ i
  | .univ 0 => LambdaPi.Term.univ .type
  | .univ 1 => LambdaPi.Term.univ .kind
  | .pi A B => .pi (term σ A) (term (lift σ) B)
  | .lam A b => .lam (term σ A) (term (lift σ) b)
  | .app f a => .app (term σ f) (term σ a)
  | _ => LambdaPi.Term.constant "__nonLF"

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion
