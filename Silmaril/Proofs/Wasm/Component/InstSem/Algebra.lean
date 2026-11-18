module

public import Silmaril.Wasm.Component.InstSem.Defs
public import Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.Pair.Thms

/-!
# The component IR with an instantiation phase: the start-free case, algebraically

For the adapter `CoreSem.toI C` (every module ready at once) the instantiating denotation is the
start-free one with a ready-at-once instantiation: `denIR_toI : c.denIR C.toI = withReady
(c.denU C)`. The proof is by equalities of strategies, node by node, from three handler
equations (`readyH_comp_liftH`, `readyH_comp_exH`, `sumMap_readyH_comp_instSplitH`), the functor
law `Strategy.ofHandler_comp` and the pairing laws `ofHandler_comp_pair`, `pair_comp_sumMap`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Wasm.Component

universe u

/-! ## Programs -/

section Prog

variable {E F G : Sig.{u}} {A B C : Type u}

theorem bind_pure : ∀ (P : Prog E A), P.bind Prog.pure = P
  | .pure _ => rfl
  | .call m k => by
    simp only [Prog.bind]
    congr 1
    funext n
    exact bind_pure (k n)

theorem bind_assoc : ∀ (P : Prog E A) (f : A → Prog E B) (g : B → Prog E C),
    (P.bind f).bind g = P.bind fun a => (f a).bind g
  | .pure _, _, _ => rfl
  | .call m k, f, g => by
    simp only [Prog.bind]
    congr 1
    funext n
    exact bind_assoc (k n) f g

theorem interp_bind (h : Handler E F) : ∀ (P : Prog F A) (f : A → Prog F B),
    (P.bind f).interp h = (P.interp h).bind fun a => (f a).interp h
  | .pure _, _ => rfl
  | .call m k, f => by
    simp only [Prog.bind, Prog.interp, bind_assoc]
    congr 1
    funext n
    exact interp_bind h (k n) f

theorem interp_interp (h₁ : Handler E F) (h₂ : Handler F G) :
    ∀ (P : Prog G A), (P.interp h₂).interp h₁ = P.interp (h₁.comp h₂)
  | .pure _ => rfl
  | .call m k => by
    simp only [Prog.interp, interp_bind, Handler.comp]
    congr 1
    funext n
    exact interp_interp h₁ h₂ (k n)

theorem interp_id : ∀ (P : Prog E A), P.interp (Handler.id E) = P
  | .pure _ => rfl
  | .call m k => by
    simp only [Prog.interp, Handler.id, Prog.lift, Prog.bind]
    congr 1
    funext n
    exact interp_id (k n)

end Prog

/-! ## Handler equations -/

variable {E F G : Sig.{0}} {R : Type}

/-- Readying then exporting is forwarding. -/
theorem readyH_comp_exH : (readyH F R).comp (exH F R) = Handler.id F := by
  funext q
  rfl

/-- A wiring handler on the export phase, below a ready-at-once instantiation. -/
theorem readyH_comp_liftH (h : Handler F G) :
    (readyH F R).comp (liftH h) = h.comp (readyH G R) := by
  funext q
  rcases q with _ | q
  · rfl
  · show ((h q).interp (exH F R)).interp (readyH F R) = (Prog.call q fun n => .pure n).interp h
    rw [interp_interp, readyH_comp_exH, interp_id]
    simp only [Prog.interp]
    exact (bind_pure _).symm

/-- Instantiation in order, when both sides are ready at once, is splitting. -/
theorem sumMap_readyH_comp_instSplitH (e : Nat) :
    (Handler.sumMap (readyH sigU Unit) (readyH sigU Unit)).comp (instSplitH e) =
      (splitH e).comp (readyH sigU Unit) := by
  funext q
  rcases q with _ | q
  · rfl
  · show (instSplitH e (some q)).interp _ = ((splitH e) q).bind fun n => (Prog.pure n).interp _
    simp only [instSplitH, splitH]
    split <;> rfl

/-! ## Strategy equations -/

open Strategy

theorem withReady_comp_liftH (σ : Strategy E F) (h : Handler F G) :
    (withReady (R := R) σ).comp (ofHandler (liftH h)) = withReady (σ.comp (ofHandler h)) := by
  rw [withReady, withReady, comp_assoc, comp_assoc, ← ofHandler_comp, ← ofHandler_comp,
    readyH_comp_liftH]

theorem extI_withReady {X : Sig.{0}} (e : Nat) (D : Strategy X sigU) (N : Strategy sigU sigU) :
    extI e (withReady D) (withReady N) = withReady (ext e D N) := by
  have h₁ : (ofHandler (readyH sigU Unit)).comp
      ((Strategy.id sigUI).pair ((ofHandler (exH sigU Unit)).comp (withReady N))) =
      ((Strategy.id sigU).pair N).comp
        (ofHandler (Handler.sumMap (readyH sigU Unit) (readyH sigU Unit))) := by
    rw [ofHandler_comp_pair, comp_id, withReady, ← comp_assoc, ← comp_assoc, ← ofHandler_comp,
      readyH_comp_exH, ofHandler_id, id_comp, pair_comp_sumMap, id_comp]
  rw [extI, show withReady D = D.comp (ofHandler (readyH sigU Unit)) from rfl,
    show withReady (R := Unit) (Wasm.Component.ext e D N) =
      (Wasm.Component.ext e D N).comp (ofHandler (readyH sigU Unit)) from rfl,
    Wasm.Component.ext, comp_assoc, ← comp_assoc (ofHandler _), h₁, comp_assoc, ← ofHandler_comp, sumMap_readyH_comp_instSplitH, ofHandler_comp]
  simp only [comp_assoc]

variable {M : Type} [CoreModule M]

theorem coreNodeI_toI (C : CoreSem M) (e : Nat) (m : M) (args : List Impl) :
    coreNodeI C.toI e m args = withReady (coreNode C e m args) := by
  rw [coreNodeI, coreNode, CoreSem.toI, withReady_comp_liftH, withReady, withReady]
  simp only [comp_assoc]

mutual
/-- **For start-free core semantics, the instantiating denotation is the start-free one with a
ready-at-once instantiation.** -/
theorem denIR_toI (C : CoreSem M) : ∀ c : Comp M, c.denIR C.toI = withReady (c.denU C)
  | .mk I ns xs => by
    rw [Comp.denIR, Comp.denU, denNodesI_toI C I.length ns, withReady_comp_liftH]

theorem denNodesI_toI (C : CoreSem M) {X : Sig.{0}} : ∀ (e : Nat) (ns : List (Node M))
    (D : Strategy X sigU), denNodesI C.toI e ns (withReady D) = withReady (denNodes C e ns D)
  | _, [], _ => by simp only [denNodesI, denNodes]
  | e, n :: ns, D => by
    rw [denNodesI, denNodes, denI_toI C e n, extI_withReady, denNodesI_toI C _ ns]

theorem denI_toI (C : CoreSem M) : ∀ (e : Nat) (n : Node M),
    n.denI C.toI e = withReady (n.den C e)
  | e, .core m args => by rw [Node.denI, Node.den, coreNodeI_toI]
  | e, .inst c args => by
    rw [Node.denI, Node.den, denIR_toI C c, withReady, withReady, comp_assoc]
end

/-! ## Monotonicity in the core semantics -/

/-- Pointwise refinement of core semantics with an instantiation phase. -/
def CoreSemI.Le (C C' : CoreSemI M) : Prop := ∀ m, C.sem m ≤ C'.sem m

theorem extI_mono {X : Sig.{0}} (e : Nat) {D D' : Strategy X sigUI}
    {N N' : Strategy sigU sigUI} (hD : D ≤ D') (hN : N ≤ N') : extI e D N ≤ extI e D' N' :=
  comp_mono hD (comp_mono (pair_mono le_rfl (comp_mono le_rfl hN)) le_rfl)

mutual
theorem denIR_mono {C C' : CoreSemI M} (h : CoreSemI.Le C C') :
    ∀ c : Comp M, c.denIR C ≤ c.denIR C'
  | .mk I ns xs => by
    simp only [Comp.denIR]
    exact comp_mono (denNodesI_mono h I.length ns le_rfl) le_rfl

theorem denNodesI_mono {C C' : CoreSemI M} (h : CoreSemI.Le C C') {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) {D D' : Strategy X sigUI}, D ≤ D' →
      denNodesI C e ns D ≤ denNodesI C' e ns D'
  | _, [], _, _, hD => by simpa only [denNodesI] using hD
  | e, n :: ns, _, _, hD => by
    simp only [denNodesI]
    exact denNodesI_mono h _ ns (extI_mono e hD (nodeDenI_mono h e n))

theorem nodeDenI_mono {C C' : CoreSemI M} (h : CoreSemI.Le C C') :
    ∀ (e : Nat) (n : Node M), n.denI C e ≤ n.denI C' e
  | e, .core m args => by
    simp only [Node.denI, coreNodeI]
    exact comp_mono le_rfl (comp_mono (h m) le_rfl)
  | e, .inst c args => by
    simp only [Node.denI]
    exact comp_mono le_rfl (denIR_mono h c)
end

end Silmaril.Proofs.Wasm.Component.InstSem
