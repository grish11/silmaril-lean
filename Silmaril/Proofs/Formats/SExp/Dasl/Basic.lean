module
public import Silmaril.Formats.SExp.Dasl.Defs

public section
namespace Silmaril.Proofs.Formats.SExp.Dasl
open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Encode Silmaril.Formats.SExpDasl

private theorem mapM_some {α : Type} : ∀ items : List α, (items.map some).mapM id = some items
  | [] => rfl
  | _ :: tail => by simp [List.mapM_cons, mapM_some tail]

theorem roundtrip {Atom : Type} (atom : TotalCodec Atom Value) (expr : SExp Atom) :
    decode? atom (encode atom expr) = some expr := by
  induction expr with
  | atom value => simp [decode?, encode, atom.recovers]
  | list len children ih =>
    simp only [encode, decode?]
    have each : (fun pos => decode? atom (encode atom (children pos))) = fun pos => some (children pos) := funext ih
    have collected : (List.ofFn fun pos => some (children pos)) = (List.ofFn children).map some :=
      (List.map_ofFn (g := some) (f := children)).symm
    rw [each, collected, mapM_some]
    simp [SExp.ofList, SExp.list.injEq]
    exact (Fin.heq_fun_iff (List.length_ofFn (f := children))).mpr (fun _ => rfl)

end Silmaril.Proofs.Formats.SExp.Dasl
