module

public import Silmaril.Wasm.Component.DWiring.Defs
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.DPair.Thms

/-!
# Divergence-observing wiring: theorems

**Consistency with the ordinary denotation.** Forgetting divergence and
infinite plays gives back the ordinary wiring operations and denotations, all
by definition:

* `toStrategy_atSizes : (DStrategy.atSizes n k σ).toStrategy = atSizes n k σ.toStrategy`;
* `toStrategy_ext`, `toStrategy_dcoreNode`;
* `toStrategy_denUD : (c.denUD C).toStrategy = c.denU C.forget` (with
  `toStrategy_denNodesD`, `toStrategy_node_denD`, by mutual induction);
* `toStrategy_denD : (c.denD C).toStrategy = c.den C.forget`;
* `toStrategy_linked_denUD`, `toStrategy_program_denUD`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

namespace DStrategy

/-- **Consistency of `atSizes`.** -/
@[simp] theorem toStrategy_atSizes (n k : Nat) (σ : DStrategy sigU sigU) :
    (atSizes n k σ).toStrategy = Component.atSizes n k σ.toStrategy := rfl

/-- **Consistency of `ext`.** -/
@[simp] theorem toStrategy_ext {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU)
    (N : DStrategy sigU sigU) :
    (ext e D N).toStrategy = Component.ext e D.toStrategy N.toStrategy := rfl

end DStrategy

variable {M : Type} [CoreModule M]

/-- Consistency of core instances. -/
@[simp] theorem toStrategy_dcoreNode (C : DCoreSem M) (e : Nat) (m : M) (args : List Impl) :
    (dcoreNode C e m args).toStrategy = coreNode C.forget e m args := rfl

mutual
/-- **Consistency of the component denotation over `sigU`.** -/
theorem toStrategy_denUD (C : DCoreSem M) : ∀ c : Comp M,
    (c.denUD C).toStrategy = c.denU C.forget
  | .mk I ns xs => by
    rw [Comp.denUD, Comp.denU]
    exact congrArg (fun S => S.comp (Strategy.ofHandler (exportsH (envAfter I.length ns) xs)))
      (toStrategy_denNodesD C I.length ns (DStrategy.ofHandler (maskH I.length)))

/-- Consistency of the extension by nodes. -/
theorem toStrategy_denNodesD (C : DCoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU),
      (denNodesD C e ns D).toStrategy = denNodes C.forget e ns D.toStrategy
  | _, [], _ => by rw [denNodesD, denNodes]
  | e, n :: ns, D => by
    rw [denNodesD, denNodes, toStrategy_denNodesD C (e + n.width) ns,
      DStrategy.toStrategy_ext, toStrategy_node_denD C e n]

/-- Consistency of node denotations. -/
theorem toStrategy_node_denD (C : DCoreSem M) :
    ∀ (e : Nat) (n : Node M), (Node.denD C e n).toStrategy = Node.den C.forget e n
  | _, .core _ _ => by rw [Node.denD, Node.den]; rfl
  | e, .inst c args => by
    rw [Node.denD, Node.den, ← toStrategy_denUD C c]
    rfl
end

/-- **Consistency of the component denotation.** -/
theorem toStrategy_denD (C : DCoreSem M) (c : Comp M) :
    (c.denD C).toStrategy = c.den C.forget := by
  rw [Comp.denD, Comp.den, DStrategy.toStrategy_atSizes, toStrategy_denUD]

/-- Consistency of the extension by core instances. -/
theorem toStrategy_linked_go (C : DCoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) (D : DStrategy X sigU),
      (Linked.denUD.go C e ns D).toStrategy = Linked.denU.go C.forget e ns D.toStrategy
  | _, [], _ => rfl
  | e, n :: ns, D => by
    rw [Linked.denUD.go, Linked.denU.go, toStrategy_linked_go C _ ns]
    rfl

/-- Consistency of the flat component denotation. -/
theorem toStrategy_linked_denUD (C : DCoreSem M) (l : Linked M) :
    (l.denUD C).toStrategy = l.denU C.forget := by
  rw [Linked.denUD, Linked.denU]
  exact congrArg
    (fun S => S.comp (Strategy.ofHandler (exportsH (linkedEnv l.imports.length l.nodes) l.exports)))
    (toStrategy_linked_go C l.imports.length l.nodes (DStrategy.ofHandler (maskH l.imports.length)))

/-- Consistency of the program denotation. -/
theorem toStrategy_program_denUD (C : DCoreSem M) (p : Program M) :
    (p.denUD C).toStrategy = p.denU C.forget := by
  unfold Program.denUD Program.denU
  cases p.observe with
  | none => exact toStrategy_denUD C _
  | some obs => rw [← toStrategy_denUD]; rfl

end Silmaril.Wasm.Component
