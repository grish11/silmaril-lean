module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.Substitution.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Interpret source globals as native named constants, rather than local binders. -/
def globals {n : ℕ} (names : Fin n → String) : Fin n → LambdaPi.Term :=
  fun i => LambdaPi.Term.constant (names i)

/-- Close every declaration against its older globals. Declaration types have
no native local variables; injective names give a single type for each name. -/
def declarations : {n : ℕ} → Context n → (Fin n → String) → String → LambdaPi.Term → Prop
  | _, .nil, _, _, _ => False
  | _, .snoc S A, names, c, T =>
      (c = names 0 ∧ T = NativeConversion.term (globals (names ∘ Fin.succ)) A) ∨
      declarations S (names ∘ Fin.succ) c T

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature
