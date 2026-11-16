module

public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
public import Silmaril.Wasm.Abstract.NodeDiv.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.Basic

/-!
# The own divergences of the modules of a linked component (proofs)

* `callMoves_eq`: the import-call moves of `Reference.Sound` are those of `StratObs`;
* `div_impSemD_sem_of`: `NodeDiv.div_core3SemD_sem` at the module's instance;
* `lowerArgs_calls`, `div_dcoreNode_impSemD`: every wiring program of `SimpleI.lowerArgs` calls
  the environment, so `implsN` is trap-silent and the core node has no silent chatter
  (`NodeTrap.div_dcoreNode_core3SemD` at the module's instance);
* `inf_spullD_of_chatter`: the importer's side of `Linked2.Chatter`, after a path of its
  instance, is an infinite play of its read-back session (`NodeDiv.instInf_of_calls`,
  `NodeDiv.mem_inf_spullD_instSession_stream`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.NodeDiv (stream prependStream)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

theorem callMoves_eq {E F : Sig.{0}} : ∀ l : List (Σ m : E.Op, E.Ar m),
    (Reference.callMoves l : List (Move E F)) = StratObs.callMoves l
  | [] => rfl
  | ⟨m, n⟩ :: l => by
    rw [Reference.callMoves, callMoves_eq l]
    simp [StratObs.callMoves]

theorem div_impSemD_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    ((impSemD P).sem m).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (importH (m.numInst h)) ∧ ∃ a b, Zip a b v ∧
        (∃ f s t, (m.numInst h).inst.Path P (.idle (m.numInst h).inst.store) a (.running f s t) ∧
          Linked2.DivB P s t) ∧
        b ∈ Strategy.ofHandler (exportH (m.numInst h))} := by
  rw [impSemD_sem_of P h, Silmaril.Wasm.Abstract.NodeDiv.div_core3SemD_sem]
  rfl

theorem lowerArgs_calls (ims : Iface) :
    ∀ im ∈ SimpleI.lowerArgs ims, ∃ r, im.target = .call r := by
  intro im him
  obtain ⟨k, -, rfl⟩ := List.mem_mapIdx.1 him
  exact ⟨k, rfl⟩

theorem div_dcoreNode_impSemD (P : Profile) (e : Nat) {m : ImpModule} (h : ∃ I, m.IsInst I)
    (ims : Iface) :
    (Node.denD (impSemD P) e (.core m (SimpleI.lowerArgs ims))).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsN e (SimpleI.lowerArgs ims) m.imports.length) ∧
        ∃ a b, Zip a b v ∧ a ∈ ((impSemD P).sem m).div ∧
          b ∈ Strategy.ofHandler (widenH m.exports.length)} := by
  rw [node_impSemD P e h,
    Silmaril.Wasm.Abstract.NodeTrap.div_dcoreNode_core3SemD P e _ _ (lowerArgs_calls ims),
    impSemD_sem_of P h]
  rfl

theorem inf_spullD_of_chatter {P : Profile} {l : Linked2} {Ie Ii : ScalarInstance}
    {d : Linked2.DivRound l Ii} {s₀ u s π : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {p₀ : List (Move Ii.E Ii.F)} (h₀ : Ii.Path P (.idle s₀) p₀ (.idle u))
    (hp : Ii.Path P (.idle u) d.instMoves (.running d.f s t))
    (hC : Linked2.Chatter P l Ie Ii d.f s t π) :
    ∃ c, (stream p₀ d.f (prependStream d.cs c)).lim ∈ (spullD (instSession Ii P s₀)).inf := by
  obtain ⟨q, c, ds, st, hq0, -, hk⟩ := hC
  refine ⟨c, Silmaril.Wasm.Abstract.NodeDiv.mem_inf_spullD_instSession_stream.2
    ⟨u, h₀, Silmaril.Wasm.Abstract.NodeDiv.instInf_of_calls ?_ hq0 fun k => ?_⟩⟩
  · rw [Linked2.DivRound.instMoves, callMoves_eq] at hp
    exact hp
  · have hk' := (hk k).1
    rwa [callMoves_eq] at hk'

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD
