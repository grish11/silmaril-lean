module

public import Silmaril.Wasm.Cfg.SessionCheck.Defs

/-!
# Exact legality of component denotations (proofs)

See `Silmaril.Wasm.Cfg.CfgLegalComp.Thms`: a property of every core module holds of every core
node of every component.
-/

public section

namespace Silmaril.Proofs.Wasm.Cfg.CfgLegalComp

open Silmaril.Wasm.Component
open Silmaril.Wasm.Cfg.SessionCheck

variable {M : Type} {p : M → Prop}

mutual
theorem compIn_of_forall (h : ∀ m, p m) : ∀ c : Comp M, CompIn p c
  | .mk _ ns _ => nodesIn_of_forall h ns

theorem nodesIn_of_forall (h : ∀ m, p m) : ∀ ns : List (Node M), NodesIn p ns
  | [] => trivial
  | n :: ns => ⟨nodeIn_of_forall h n, nodesIn_of_forall h ns⟩

theorem nodeIn_of_forall (h : ∀ m, p m) : ∀ n : Node M, NodeIn p n
  | .core m _ => h m
  | .inst c _ => compIn_of_forall h c
end

end Silmaril.Proofs.Wasm.Cfg.CfgLegalComp
