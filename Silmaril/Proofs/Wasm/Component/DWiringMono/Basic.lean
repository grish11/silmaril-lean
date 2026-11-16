module

public import Silmaril.Wasm.Component.DWiringMono.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DPair.Thms

/-!
# Monotonicity of the divergence-observing denotation (proofs)

By mutual induction mirroring `Comp.denUD`/`denNodesD`/`Node.denD`, from the monotonicity of
`DStrategy.comp` (`DStrategy.comp_mono`) and `DStrategy.pair` (`DStrategy.pair_mono`), as
`Component.denU_mono` for the ordinary denotation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringMono

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

theorem ext_mono {X : Sig.{0}} (e : Nat) {D D' : DStrategy X sigU} {N N' : DStrategy sigU sigU}
    (hD : D ≤ D') (hN : N ≤ N') : DStrategy.ext e D N ≤ DStrategy.ext e D' N' :=
  DStrategy.comp_mono hD (DStrategy.comp_mono (DStrategy.pair_mono le_rfl hN) le_rfl)

theorem dcoreNode_mono {C C' : DCoreSem M} (h : C.Le C') (e : Nat) (m : M) (args : List Impl) :
    dcoreNode C e m args ≤ dcoreNode C' e m args :=
  DStrategy.comp_mono le_rfl (DStrategy.comp_mono (h m) le_rfl)

mutual
theorem denUD_mono {C C' : DCoreSem M} (h : C.Le C') :
    ∀ c : Comp M, c.denUD C ≤ c.denUD C'
  | .mk I ns xs => by
    simp only [Comp.denUD]
    exact DStrategy.comp_mono (denNodesD_mono h I.length ns le_rfl) le_rfl

theorem denNodesD_mono {C C' : DCoreSem M} (h : C.Le C') {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) {D D' : DStrategy X sigU}, D ≤ D' →
      denNodesD C e ns D ≤ denNodesD C' e ns D'
  | _, [], _, _, hD => by simpa only [denNodesD] using hD
  | e, n :: ns, _, _, hD => by
    simp only [denNodesD]
    exact denNodesD_mono h _ ns (ext_mono e hD (node_denD_mono h e n))

theorem node_denD_mono {C C' : DCoreSem M} (h : C.Le C') :
    ∀ (e : Nat) (n : Node M), Node.denD C e n ≤ Node.denD C' e n
  | e, .core m args => by
    simp only [Node.denD]
    exact dcoreNode_mono h e m args
  | e, .inst c args => by
    simp only [Node.denD]
    exact DStrategy.comp_mono le_rfl (denUD_mono h c)
end

theorem linked_go_mono {C C' : DCoreSem M} (h : C.Le C') {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) {D D' : DStrategy X sigU}, D ≤ D' →
      Linked.denUD.go C e ns D ≤ Linked.denUD.go C' e ns D'
  | _, [], _, _, hD => by simpa only [Linked.denUD.go] using hD
  | e, n :: ns, _, _, hD => by
    simp only [Linked.denUD.go]
    exact linked_go_mono h _ ns (ext_mono e hD (dcoreNode_mono h e n.1 n.2))

theorem program_denUD_mono {C C' : DCoreSem M} (h : C.Le C') (p : Program M) :
    p.denUD C ≤ p.denUD C' := by
  unfold Program.denUD
  cases p.observe with
  | none => exact denUD_mono h _
  | some obs => exact DStrategy.comp_mono (denUD_mono h _) le_rfl

end Silmaril.Proofs.Wasm.Component.DWiringMono
