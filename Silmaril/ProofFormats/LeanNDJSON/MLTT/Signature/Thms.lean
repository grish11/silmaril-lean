module

public import Std.Data.String.ToNat
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Signature.Defs
import Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.Signature

public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory

variable {Name : Type} {S T : Signature Name}

/-- Distinct declaration indices use distinct MLTT variables. -/
theorem Signature.symbolSlot_injective : Function.Injective symbolSlot :=
  fun _ _ h => Nat.repr_injective ((String.append_right_inj "symbol:").mp h)

/-- A definition equation never shadows a declared constant. -/
theorem Signature.equationSlot_ne_symbolSlot (i j : Nat) :
    equationSlot i ≠ symbolSlot j := by
  intro h
  simpa [equationSlot, symbolSlot, String.toList_append] using congrArg (·.toList.head?) h

/-- A successful lookup selects exactly the requested name. -/
theorem Signature.resolve?_name [DecidableEq Name] {name : Name}
    {i : Fin S.declarations.length} (h : S.resolve? name = some i) :
    S.declarations[i].name = name :=
  of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp h).1

/-- Signature extensions preserve successful resolutions and slot numbers. -/
theorem Signature.resolve?_weaken [DecidableEq Name] {name : Name}
    {i : Fin S.declarations.length} (f : S ⟶ T) (h : S.resolve? name = some i) :
    T.resolve? name = some (i.castLE f.down.length_le) :=
  Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.resolve?_weaken f h

/-- Auxiliary event hypotheses can be replaced by their derivations. -/
theorem derives_cut {H K : Set (Sentence S)} {s : Sentence S}
    (hK : ∀ k ∈ K, Derives H k) (h : Derives (H ∪ K) s) : Derives H s :=
  Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.derives_cut hK h

/-- Extending a signature transports and reflects derivability of events in
their original declaration scopes. -/
theorem derives_weaken_iff (f : S ⟶ T) (H : Set (Sentence S)) (s : Sentence S) :
    Derives H s ↔ Derives (Sentence.weaken f '' H) (s.weaken f) :=
  Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.derives_weaken f H s

end Silmaril.ProofFormats.LeanNDJSON.MLTT
