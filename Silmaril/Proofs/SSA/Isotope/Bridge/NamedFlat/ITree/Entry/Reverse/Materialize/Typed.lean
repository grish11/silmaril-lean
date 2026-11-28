module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
open LambdaSSA (FiniteCFG Flat)
open LetCase.LocallyNameless (Tm HasType)

universe u v
variable {τ : Type u} [TypeFormers τ] {F : Type v} [HasTy F τ]
  {labels blocks exits n : Nat} {β : BoundCtx τ n} {L : Fin labels → τ}

private theorem alias_typed {i : Fin n} {tail : Tm Empty F (n + 1)} {A B : τ}
    (arg : HasType F .nil β (.bv i : Tm Empty F n) A) (typed : HasType F .nil (β.snoc A) tail B) :
    HasType F .nil β (tail.rename (aliasIndex i)) B := by
  cases arg
  exact typed.rename ⟨aliasIndex i, Fin.cases rfl fun _ => rfl⟩

private theorem jump_hasType (canBind : Bool) {target : Fin labels} {arg : Tm Empty F n}
    (typed : HasType F .nil β arg (L target)) : (jump canBind target arg).HasType L β := by
  cases arg <;> try exact .br typed
  case let₁ a tail =>
    cases typed with
    | let₁ arg tailTyped =>
      cases canBind with
      | true => exact .let₁ arg (.br tailTyped)
      | false =>
        cases a <;> try exact .br (.let₁ arg tailTyped)
        case bv i => exact .br (alias_typed arg tailTyped)

private theorem body_hasType (canBind : Bool) {t : Flat F labels n} (typed : t.HasType L β) :
    (body canBind t).HasType L β := by
  induction typed generalizing canBind with
  | br typed => exact jump_hasType canBind typed
  | let₁ arg _ ih => exact .let₁ arg (ih canBind)
  | let₂ arg _ ih => exact .let₂ arg (ih canBind)
  | case discr _ _ left right => exact .case discr (left false) (right false)

theorem graph_hasType {g : FiniteCFG F blocks exits n} {R : Fin blocks → τ} {D : Fin exits → τ}
    (typed : g.HasType β R D) : (graph g).HasType β R D :=
  ⟨body_hasType true typed.entry, fun i => body_hasType true (typed.block i)⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
