module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.Back

/-!
# Diverging linked calls, backwards: rounds

From the importer's core activation at the shared thread `y` (in a frame `extN B ιe N C`),
`LInv` relating it to the importer's part `x` and the exporter's store `π`, and the machine
diverging there (`DInv`):

* `ldiv_round`: one of
  - **(i)** B's core activation runs forever: B's part runs host-free forever
    (`Linked2.DivB`, `link_inf_back`);
  - **(ii)** B runs to a callout whose arguments lift, and the nested activation of A runs
    forever: A's export diverges from `π` (`Linked2.DivA`, `link_inf_back` from `exp_invoke`);
  - **(iii)** the nested call returns values that lift and the machine diverges after it, back
    in B's core activation: one served import call (`ImpRel`, `ExpRunT`) to a state where
    `DInv` holds again (`LInv.resume`).

  The other ends do not diverge: a callout whose arguments do not lift, a trap of A, or results
  of A that do not lift trap (`nest_trap_args`, `nest_at`, `TrapsFrom.not_diverges`); A never
  calls out (`LinkSite`); and an exit of B's core phase other than a callout does not diverge
  by the hypothesis `ExitsQuiet` (discharged for linked calls in `Main`);
* `ldiv_classify`: by classical case analysis on whether a finite chain of served calls reaches
  a state of (i) or (ii), and otherwise by dependent choice (`seq_of_step`), a divergence is a
  finite prefix of served calls followed by (i), (ii) or (iii) **chatter** (`Linked2.Chatter`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type}

/-- A state of a diverging linked call inside the importer's core activation: the shared thread
`y`, the importer's part `x`, the exporter's store `π`, and the frame data `ιe`, `N`, `C`. -/
structure DSt (P : Profile) (σ : Type) where
  y : CoreSt (E3 P)
  x : Store Nat × STh
  π : Store Nat
  ιe : InstState
  N : List (NRec P)
  C : List (Option (Activation (E3 P) σ))

variable (prof : ProfileKind) (impl : HostImpl (E3 P) σ) (l : Linked2)
  (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ : Store Nat)
  (F₀ : List (FuncInst (CanonHost (E3 P)))) (Op₀ Oc₀ : Own) (f : Ii.F.Op)
  (B : Machine.Config (E3 P) σ) (th : Option ThreadId)
  (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
  (rest : List (Activation (E3 P) σ))

/-- **The invariant of a diverging linked call**: the machine diverges from the importer's core
activation at `z.y`, the exporter's thread table is reusable, and `LInv` holds. -/
structure DInv (z : DSt P σ) : Prop where
  div : Diverges prof (fun _ _ => false) (DI P impl)
    (coreCfg (extN B z.ιe z.N z.C) th K segs rest z.y)
  th : ThreadsOk z.ιe
  inv : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f z.y z.x z.π

/-- **The exits of the importer's core phase other than callouts do not diverge** (from a state
where `LInv` holds). -/
def ExitsQuiet : Prop :=
  ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (x : Store Nat × STh) (π : Store Nat) (lb : Label (E3 P) σ)
    (m₁ : Machine.Config (E3 P) σ), LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π →
    (∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys) →
    CoreExit (extN B ιe N C) th K segs rest y lb m₁ →
    ¬ Diverges prof (fun _ _ => false) (DI P impl) m₁

variable {prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest}

/-- **One round of a diverging linked call**: (i), (ii), or a served import call back to the
invariant. -/
theorem ldiv_round (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hB : LFrame B th)
    (hex : ExitsQuiet prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest) {z : DSt P σ}
    (hz : DInv prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest z) :
    Linked2.DivB P z.x.1 z.x.2 ∨ Linked2.DivA P l Ie Ii f z.x.1 z.x.2 z.π ∨
      ∃ (c : Σ e : Ii.E.Op, Ii.E.Ar e)
        (ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)) (z' : DSt P σ),
        Ii.Path P (.running f z.x.1 z.x.2) (callMoves [c]) (.running f z'.x.1 z'.x.2) ∧
        Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds ∧
        Linked2.ExpRunT P l Ie z.π ds z'.π ∧
        DInv prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest z' := by
  rcases z with ⟨y, x, π, ιe, N, C⟩
  obtain ⟨hd, hte, hI⟩ := hz
  dsimp only at hd hte hI ⊢
  rcases coreCfg_diverges_step hd with hinf | ⟨y₁, lb, m₁, hy, hx, dy₁, d₁⟩
  · -- (i) B's core activation runs forever
    left
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
    obtain ⟨ts, hs, ht⟩ := hI.typed S
    exact link_inf_back (gL P l) hinf hL hs ht
  obtain ⟨x₁, hI₁, hr₁⟩ := hI.reach S hy
  by_cases hco : ∃ h ys, (E3 P).status y₁.1 y₁.2 = .callout h ys
  swap
  · exact absurd d₁ (hex ιe N C y₁ x₁ π lb m₁ hI₁ (fun h ys e => hco ⟨h, ys, e⟩) hx)
  obtain ⟨h, ys, hst⟩ := hco
  obtain ⟨k, nm, p, w, xe, E, a', args, e, rfl, hk, hw, hxe, rfl, hdx, hm, he', -⟩ :=
    hI₁.callout S hst
  have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ (List.mem_of_getElem? hk)).2.2
  have hfl : ArenaField.funcs.get? B.store (l.wireFid k) =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) := S.lifted k w xe hw hxe
  obtain ⟨hpf, hys', hmaxp, hrf, hmaxr, hexp⟩ :=
    site_of ((LInv.linkOk S hI₁) [] y₁ _ ys (.done .refl) hst) hfl hres
  have hek := ifaceOp?_some he'
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hxw : l.exp.exports[(⟨w, hwl⟩ : Fin l.exp.exports.length)] = xe :=
    (List.getElem?_eq_some_iff.mp hxe).2
  have hw' : l.wire[e.1.val]? = some w := hek.1 ▸ hw
  have hk' : l.imp.imports[e.1.val]? = some (nm, xe.ty) := hek.1 ▸ hk
  have hco : Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 k args := ⟨E, a', hdx⟩
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  have hadd := addThread?_ok hte ⟨(extN B ιe N C).store.threads.length⟩
  have hrem := removeThread?_enter ιe ⟨(extN B ιe N C).store.threads.length⟩
  cases hws : liftArgs xe.ty.params ys with
  | none =>
    exact absurd dy₁ (TrapsFrom.not_diverges (nest_trap_args (prof := prof) (impl := impl) B ιe _
      N C th K segs rest y₁ (l.wireFid k) _ xe.ty ys ιi hst (hB.entry _ _ _ _ _) hi hleave hfl
      hB.len hadd hpf hys' hmaxp hws))
  | some ws =>
    obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₁, hrun, hctl, hcore, -, hret, htrap⟩ :=
      nest_at (prof := prof) (impl := impl) B ιe _ N C th K segs rest y₁ (l.wireFid k) _ xe.ty ys
        ιi ws hst (hB.entry _ _ _ _ _) hi hleave hfl hB.len hadd hrem hpf hys' hmaxp hws hres hrf
        hmaxr
    have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y₁.1,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) := by
      rw [← hcore]
      exact eq_coreCfg hctl
    have dM : Diverges prof (fun _ _ => false) (DI P impl) M₁ := hrun.diverges dy₁
    rw [hM] at dM
    have typed : ValTy.checkList xe.ty.params ws = true :=
      Silmaril.Wasm.Component.checkList_of_liftArgs hws
    rcases coreCfg_diverges_step dM with hinfA | ⟨e₁, lb', m₂, he₁, hx₂, -, d₂⟩
    · -- (ii) the nested activation of A runs forever
      right; left
      obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI₁.rel
      obtain ⟨nm', hcx⟩ := S.expGood.core xe hxm
      have hkc : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
      obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hI₁.wf
        (opAt S.expInst hkc (exp_hxs hcx typed hkc))
      have hL₀ := exp_invoke hR.rp hI₁.fnE (hR.fnp ▸ S.owned xe hxm) (lowerArgs xe.ty.params ws)
      have hrunA := link_inf_back (gL P l) hinfA hL₀ hI₁.wf.storeOk htyped
      refine ⟨e, x₁.1, x₁.2, nm, xe.ty, ws, ⟨w, hwl⟩, .cons (.ucall hr₁ hco he') (.nil _), hk',
        ?_, hw', ?_⟩
      · rw [hek.2, filterMap_of_mapM hm]
        exact hws
      · rw [hxw]
        exact ⟨typed, hrunA⟩
    · obtain ⟨hnco, hty⟩ := hexp ws hws e₁ he₁
      rcases hx₂ with ⟨zs, hzs, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h', ys', hc'⟩
      · cases hus : liftArgs xe.ty.results zs with
        | none =>
          exact absurd d₂ (TrapsFrom.not_diverges (htrap e₁ zs (hty zs hzs) hus).trapsFrom)
        | some us =>
          -- (iii) one served import call
          right; right
          obtain ⟨tr₄, h₄⟩ := hret e₁ zs us (hty zs hzs) hus
          obtain ⟨π', hI₂, hRet⟩ := hI₁.resume S hk hxe hdx he' hws he₁ hzs hus
          have hcheck : ValTy.checkList xe.ty.results us = true :=
            Silmaril.Wasm.Component.checkList_of_liftArgs hus
          refine ⟨⟨e, .values ⟨_, resAnswer S hk hek.1 hcheck⟩⟩, _,
            ⟨(e₁.1, (E3 P).resume e₁.1 y₁.2 (.values (lowerArgs xe.ty.results us))),
              (x₁.1, Silmaril.Wasm.SingleThreaded.resumeResult x₁.1 x₁.2
                (.values ((lowerArgs xe.ty.results us).map
                  Silmaril.Wasm.SingleThreaded.ofFlat))), π', _, _, C₁⟩,
            .cons (.ucall hr₁ hco he') (.cons (.uret _) (.nil _)),
            impRel_link hk hek.1 hek.2 hm hws hcheck _ rfl,
            .ret ⟨w, hwl⟩ hw' (hxw ▸ hRet) (.nil π'), ⟨h₄.diverges d₂, threadsOk_after _ _, hI₂⟩⟩
      · exact absurd d₂ (not_diverges_trapCfg _)
      · exact absurd hc' (hnco h' ys')

/-! ## Classification -/

/-- **A divergence from the importer's core activation** is a finite prefix of served import
calls followed by (i) B diverging host-free, (ii) A diverging inside an import call, or
(iii) chatter. -/
theorem ldiv_classify (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hB : LFrame B th)
    (hex : ExitsQuiet prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest) {z₀ : DSt P σ}
    (hz₀ : DInv prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest z₀) :
    ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (x : Store Nat × STh) (π : Store Nat),
      Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f x.1 x.2) ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss ∧
      Linked2.ExpRunT P l Ie z₀.π dss.flatten π ∧
      (Linked2.DivB P x.1 x.2 ∨ Linked2.DivA P l Ie Ii f x.1 x.2 π ∨
        Linked2.Chatter P l Ie Ii f x.1 x.2 π) := by
  classical
  let Pre : DSt P σ → Prop := fun z => ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
    (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))),
    Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f z.x.1 z.x.2) ∧
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss ∧
    Linked2.ExpRunT P l Ie z₀.π dss.flatten z.π
  by_cases hfin : ∃ z, Pre z ∧ (Linked2.DivB P z.x.1 z.x.2 ∨ Linked2.DivA P l Ie Ii f z.x.1 z.x.2 z.π)
  · obtain ⟨z, ⟨cs, dss, h₁, h₂, h₃⟩, hd⟩ := hfin
    exact ⟨cs, dss, z.x, z.π, h₁, h₂, h₃, hd.elim .inl (fun h => .inr (.inl h))⟩
  · let T : DSt P σ → (Σ e : Ii.E.Op, Ii.E.Ar e) ×
        List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → DSt P σ → Prop :=
      fun z g z' => Ii.Path P (.running f z.x.1 z.x.2) (callMoves [g.1]) (.running f z'.x.1 z'.x.2) ∧
        Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii g.1 g.2 ∧
        Linked2.ExpRunT P l Ie z.π g.2 z'.π
    have step : ∀ z, (Pre z ∧ DInv prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest z) →
        ∃ g z', T z g z' ∧
          (Pre z' ∧ DInv prof impl l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f B th K segs rest z') := by
      rintro z ⟨⟨cs, dss, h₁, h₂, h₃⟩, hz⟩
      rcases ldiv_round S hB hex hz with h | h | ⟨c, ds, z', hp, hr, he, hz'⟩
      · exact absurd ⟨z, ⟨cs, dss, h₁, h₂, h₃⟩, .inl h⟩ hfin
      · exact absurd ⟨z, ⟨cs, dss, h₁, h₂, h₃⟩, .inr h⟩ hfin
      refine ⟨(c, ds), z', ⟨hp, hr, he⟩, ⟨cs ++ [c], dss ++ [ds], ?_, List.rel_append h₂ (.cons hr .nil),
        ?_⟩, hz'⟩
      · rw [callMoves_append]
        exact path_append h₁ hp
      · rw [List.flatten_append, List.flatten_singleton]
        exact expRunT_append h₃ he
    obtain ⟨sq, gs, h0, hs⟩ := seq_of_step _ T step
      (⟨⟨[], [], .nil _, .nil, .nil _⟩, hz₀⟩ : Pre z₀ ∧ _)
    refine ⟨[], [], z₀.x, z₀.π, .nil _, .nil, .nil _, .inr (.inr ?_)⟩
    refine ⟨fun n => .running f (sq n).x.1 (sq n).x.2, fun n => (gs n).1, fun n => (gs n).2,
      fun n => (sq n).π, by simp only [h0], by simp only [h0], fun n => hs n⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
