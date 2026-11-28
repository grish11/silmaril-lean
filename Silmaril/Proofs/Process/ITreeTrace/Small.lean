module

public import Mathlib.Logic.Small.Basic
public import Silmaril.Process.ITreeTrace.Defs

namespace Silmaril.Process.ITreeTrace.Proofs

open TypedSyscall (Signature)
open Silmaril.Elgot.ITree (Approx Visible Tree)

variable {sig : Signature} {A X Y : Type}

-- Store the request itself in each approximation, eliminating the universe
-- contributed by the existential reply type in `Visible`.
private abbrev Layer (sig : Signature) (A X : Type) := A ⊕ (Σ req : sig.Request, sig.Response req → X)

private def packLayer {Big : Type 1} (f : Big → Y) : Visible (Event sig) A Big → Layer sig A Y
  | .ret a => .inl a
  | .vis (.call req) next => .inr ⟨req, f ∘ next⟩

private def unpackLayer {Big : Type 1} (f : X → Big) : Layer sig A X → Visible (Event sig) A Big
  | .inl a => .ret a
  | .inr ⟨req, next⟩ => .vis (.call req) (f ∘ next)

private def Packed (sig : Signature) (A : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => Part (Layer sig A (Packed sig A n))

private def pack : (n : Nat) → Approx (Event sig) A n → Packed sig A n
  | 0, _ => ()
  | n + 1, root => root.map (packLayer (pack n))

private def unpack : (n : Nat) → Packed sig A n → Approx (Event sig) A n
  | 0, _ => PUnit.unit
  | n + 1, root => root.map (unpackLayer (unpack n))

private theorem unpack_pack (n : Nat) (root : Approx (Event sig) A n) :
    unpack n (pack n root) = root := by
  induction n with
  | zero => cases root; rfl
  | succ n ih =>
      simp only [pack, unpack, Part.map_map]
      refine Part.map_id' (fun layer => ?_) root
      cases layer with
      | ret _ => rfl
      | vis event next =>
          cases event
          simp [packLayer, unpackLayer, Function.comp_def, ih]

public theorem smallProgram (sig : Signature) (A : Type) : Small.{0} (Program sig A) := by
  apply small_of_injective (f := fun (t : Program sig A) (n : Nat) => pack n (t.observe n))
  intro first second same
  apply Tree.ext
  intro n
  simpa only [unpack_pack] using congrArg (unpack n) (congrFun same n)

end Silmaril.Process.ITreeTrace.Proofs
