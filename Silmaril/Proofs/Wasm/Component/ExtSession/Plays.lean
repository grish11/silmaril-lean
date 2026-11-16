module

public import Silmaril.Wasm.Component.ExtSession.Defs
public import Silmaril.Games.Pair.Thms
public import Silmaril.Games.Handler.Thms

/-!
# The component environment extension on sessions: finite plays (proofs)

`toStrategy_ext_eq`: the finite plays of `DStrategy.ext e` with session answers relabelled are
the relabelled finite plays of `SessionExt.extS (splitR e)`. At the level of finite plays the
handler laws of `Silmaril.Games.Pair` and `Silmaril.Games.Handler` apply: `toU` below the
pairing is duplicated (`Strategy.ofHandler_comp_pair`), cancels `ofU`
(`toU_comp_ofU`), and is moved above the pairing (`Strategy.pair_comp_sumMap`), where it
commutes with the routing (`sumMap_comp_splitH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.ExtSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionRoute
  Silmaril.Games.Abstract.SessionExt Silmaril.Wasm.Component

theorem ofOpt_toOpt (x : Payload ⊕ PUnit.{1}) : ofOpt (toOpt x) = x := by
  rcases x with b | ⟨⟩ <;> rfl

/-- **The relabelling handlers cancel.** -/
theorem toU_comp_ofU : toU.comp ofU = Handler.id sigS := by
  funext q
  simp only [Handler.comp, ofU, toU, ansH, Prog.interp, Prog.bind, Handler.id, Prog.lift,
    ofOpt_toOpt]

/-- **Relabelling commutes with the routing.** -/
theorem sumMap_comp_splitH (e : Nat) :
    (Handler.sumMap toU toU).comp (splitH e) = (routeH (splitR e)).comp toU := by
  funext q
  have hR : ((routeH (splitR e)).comp toU) q =
      (fun a₀ : (sigS ⊕ₛ sigS).Op => Prog.call a₀ fun n => Prog.pure (toOpt (unsum a₀ n)))
        (splitR e q) := rfl
  rw [hR]
  by_cases h : q.1 < e
  · rw [show splitR e q = .inl q by simp [splitR, h]]
    simp [Handler.comp, splitH, toU, ansH, Handler.sumMap, Prog.interp, Prog.bind,
      Handler.ofHom, Sig.Hom.inl, unsum, h]
  · rw [show splitR e q = .inr (q.1 - e, q.2) by simp [splitR, h]]
    simp [Handler.comp, splitH, toU, ansH, Handler.sumMap, Prog.interp, Prog.bind,
      Handler.ofHom, Sig.Hom.inr, unsum, h]

/-- **The finite plays of the extension, relabelled.** -/
theorem toStrategy_ext_eq {X : Sig.{0}} (e : Nat) (D₀ : DStrategy X sigS)
    (N₀ : DStrategy sigS sigS) :
    (DStrategy.ext e (D₀.comp (DStrategy.ofHandler toU))
        ((DStrategy.ofHandler ofU).comp (N₀.comp (DStrategy.ofHandler toU)))).toStrategy =
      ((extS (splitR e) D₀ N₀).comp (DStrategy.ofHandler toU)).toStrategy := by
  show (D₀.toStrategy.comp (Strategy.ofHandler toU)).comp
      (((Strategy.id sigU).pair ((Strategy.ofHandler ofU).comp
        (N₀.toStrategy.comp (Strategy.ofHandler toU)))).comp (Strategy.ofHandler (splitH e))) =
    (D₀.toStrategy.comp (((Strategy.id sigS).pair N₀.toStrategy).comp
      (Strategy.ofHandler (routeH (splitR e))))).comp (Strategy.ofHandler toU)
  have hc : (Strategy.ofHandler toU).comp ((Strategy.ofHandler ofU).comp
      (N₀.toStrategy.comp (Strategy.ofHandler toU))) =
        N₀.toStrategy.comp (Strategy.ofHandler toU) := by
    rw [← Strategy.comp_assoc, ← Strategy.ofHandler_comp, toU_comp_ofU, Strategy.ofHandler_id,
      Strategy.id_comp]
  have hp : (Strategy.ofHandler toU).pair (N₀.toStrategy.comp (Strategy.ofHandler toU)) =
      ((Strategy.id sigS).pair N₀.toStrategy).comp
        (Strategy.ofHandler (Handler.sumMap toU toU)) := by
    rw [Strategy.pair_comp_sumMap, Strategy.id_comp]
  rw [Strategy.comp_assoc, ← Strategy.comp_assoc (Strategy.ofHandler toU),
    Strategy.ofHandler_comp_pair, Strategy.comp_id, hc, hp, Strategy.comp_assoc,
    ← Strategy.ofHandler_comp, sumMap_comp_splitH, Strategy.ofHandler_comp]
  simp only [Strategy.comp_assoc]

end Silmaril.Proofs.Wasm.Component.ExtSession
