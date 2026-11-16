module

public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Component.DWiringMulti.Thms
public import Silmaril.Wasm.Abstract.NodeTrap.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess

/-!
# The divergence-observing IR semantics of modules with imports (proofs)

* `forget_impSemD`: case analysis on the instance, `forget_core3SemD` when there is one, the
  trapping handler otherwise;
* `node_impSemD`: a core node of `impSemD P` is the core node of `core3SemD P` at the module's
  instance;
* `div_denUD_simpleI`: `div_denUD` on one core node, with `obs_ext_maskH` (the node propagates
  traps, `node_impSemD` and `NodeTrap.trapPropagating_core3SemD`);
* `div_denD_sources`: `div_denD_nodes` with the two nodes of `Linked2.toComp` unfolded;
* `refSessProd_iff_plays`: `refSessProd_iff_prefix` with each prefix read by
  `sessAdequacy_full` and `refOuts_inj`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession (core3SemD forget_core3SemD)
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy (refOuts_inj)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

theorem impSem_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    (impSem P).sem m = (core3Sem P).sem (m.numInst h) := by
  simp only [impSem]
  split
  · rfl
  · contradiction

theorem impSemD_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    (impSemD P).sem m = (core3SemD P).sem (m.numInst h) := by
  simp only [impSemD, h, ↓reduceDIte]
  rfl

theorem impSemD_sem_of_not (P : Profile) {m : ImpModule} (h : ¬ ∃ I, m.IsInst I) :
    (impSemD P).sem m = DStrategy.ofHandler fun _ => .pure none := by
  simp only [impSemD, h, ↓reduceDIte]

theorem forget_impSemD (P : Profile) : (impSemD P).forget = impSem P := by
  have key : ∀ m, ((impSemD P).sem m).toStrategy = (impSem P).sem m := by
    intro m
    by_cases hm : ∃ I, m.IsInst I
    · rw [impSemD_sem_of P hm, impSem_sem_of P hm, ← forget_core3SemD P]
      rfl
    · rw [impSemD_sem_of_not P hm]
      simp only [impSem]
      split
      · contradiction
      · rfl
  exact congrArg CoreSem.mk (funext key)

theorem node_impSemD (P : Profile) (e : Nat) {m : ImpModule} (h : ∃ I, m.IsInst I)
    (args : List Impl) :
    Node.denD (impSemD P) e (.core m args) =
      Node.denD (core3SemD P) e (.core (m.numInst h) args) := by
  simp only [Node.denD]
  unfold dcoreNode
  rw [impSemD_sem_of P h]
  rfl

theorem div_denUD_simpleI (P : Profile) (c : SimpleI) (h : ∃ I, c.mod.IsInst I) :
    ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).div =
      {p | ∃ s t, Zip s t p ∧
        s ∈ NodeDiv c.imports.length (Strategy.ofHandler (maskH c.imports.length))
          (Node.denD (impSemD P) c.imports.length c.coreNode) ∧
        t ∈ Strategy.ofHandler
          (exportsH (envAfter c.imports.length [c.coreNode]) c.compExports)} := by
  have hN : TrapPropagating (Node.denD (impSemD P) c.imports.length c.coreNode) := by
    rw [SimpleI.coreNode, node_impSemD P _ h]
    exact Silmaril.Wasm.Abstract.NodeTrap.trapPropagating_core3SemD P _ _ _
  rw [div_denUD, denNodesD_cons, div_denNodesD, nodesObs_nil, obs_ext_maskH _ hN]
  rfl

theorem div_denD_sources (C : DCoreSem ImpModule) (l : Linked2) :
    ((Comp.mk [] [l.expNode, l.impNode] l.compExports).denD C).div =
      {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
        u ∈ Strategy.ofHandler (widenH 0) ∧
          t ∈ Strategy.ofHandler (narrowH l.compExports.length) ∧ ∃ d x, Zip d x v ∧
            d ∈ l.linkDiv C ∧
            x ∈ Strategy.ofHandler
              (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports)} := by
  rw [div_denD_nodes, nodesObs_cons, nodesObs_cons, nodesObs_nil]
  simp only [List.length_nil, Nat.zero_add]
  rfl

theorem refSessProd_iff_plays (o : GrowOracle) (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∀ k, Linked2.sessMoves l (streamTake a k) (streamTake out k) ∈
        l.toComp.den (impSem (profile o)) := by
  rw [Linked2.refSessProd_iff_prefix o hl a out ht impl h₀]
  refine forall_congr' fun k => ?_
  have htk : SimpleI.TypedCalls l.imp (streamTake a k) := fun q hq => by
    obtain ⟨i, -, rfl⟩ := streamTake_mem hq
    exact ht i
  rw [Linked2.sessAdequacy_full (profile o) prof l hl impl h₀ _ htk]
  constructor
  · rintro ⟨outs, he, -, hm⟩
    obtain rfl := refOuts_inj he
    exact hm
  · intro hm
    exact ⟨_, rfl, by simp [streamTake], hm⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD
