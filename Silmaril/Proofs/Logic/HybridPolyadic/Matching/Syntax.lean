module

public import Silmaril.Logic.HybridPolyadic.Matching.Defs

public section
namespace Silmaril.Proofs.Logic.HybridPolyadic.Matching
open CategoryTheory
open Silmaril.Logic.HybridPolyadic Silmaril.Logic.HybridPolyadic.Matching
open Silmaril.Logic.Matching

private theorem map_nominal {S T : Signature} (f : S ⟶ T) {n : ℕ} (a : S.Nominal) :
    FirstOrder.Pattern.map (matchingSignatureMap f) (nominalPattern (n := n) a) =
      nominalPattern (f.nominal a) := by
  change FirstOrder.Pattern.app (A := matchingSignature T) (Operation.nominal (f.nominal a)) _ = _
  apply congrArg (FirstOrder.Pattern.app (A := matchingSignature T) (Operation.nominal (f.nominal a)))
  funext i
  exact Fin.elim0 i

private theorem map_defined {S T : Signature} (f : S ⟶ T) {n : ℕ} (p : Pattern S n) :
    FirstOrder.Pattern.map (matchingSignatureMap f) (definedPattern p) =
      definedPattern (FirstOrder.Pattern.map (matchingSignatureMap f) p) := by
  change FirstOrder.Pattern.app (A := matchingSignature T) Operation.defined _ = _
  apply congrArg (FirstOrder.Pattern.app (A := matchingSignature T) (Operation.defined (S := T)))
  funext i
  rw [Fin.eq_zero i]
  rfl

/-- Signature maps commute with the syntactic FO translation, including @ and down. -/
theorem translate_map {S T : Signature} (f : S ⟶ T) {n : ℕ} (p : Formula S n) :
    FirstOrder.Pattern.map (matchingSignatureMap f) (translate p) = translate (p.map f) := by
  induction p with
  | atom a =>
    change FirstOrder.Pattern.app (A := matchingSignature T) (Operation.atom (f.atom a)) _ = _
    apply congrArg (FirstOrder.Pattern.app (A := matchingSignature T) (Operation.atom (f.atom a)))
    funext i
    exact Fin.elim0 i
  | bot => rfl
  | imp p q hp hq =>
    exact congrArg₂ (fun p q => FirstOrder.Pattern.neg (.conj p (.neg q))) hp hq
  | nominal a => exact map_nominal f a
  | state _ => rfl
  | atNom a p hp =>
    change FirstOrder.Pattern.map (matchingSignatureMap f) (definedPattern _) = _
    rw [map_defined]
    change definedPattern (.conj (FirstOrder.Pattern.map (matchingSignatureMap f) (nominalPattern a))
      (FirstOrder.Pattern.map (matchingSignatureMap f) (translate p))) = _
    rw [map_nominal, hp]
    rfl
  | atState i p hp =>
    change FirstOrder.Pattern.map (matchingSignatureMap f) (definedPattern _) = _
    rw [map_defined]
    exact congrArg (fun p => definedPattern (.conj (.var i) p)) hp
  | dia a ps ih => exact congrArg (FirstOrder.Pattern.app (A := matchingSignature T) (Operation.action (f.action _ a))) (funext ih)
  | down p hp => exact congrArg (fun p => FirstOrder.Pattern.ex () (.conj (.var 0) p)) hp


end Silmaril.Proofs.Logic.HybridPolyadic.Matching
