module

public import Silmaril.Wasm.Component.InstExport.Defs
public import Silmaril.Proofs.Wasm.Component.InstSem.Plays
public import Silmaril.Proofs.Wasm.Component.InstEngine.Converse

/-!
# The export phase of an instantiable strategy: proofs

* `withReady_second`: in `withReady σ`, `inst` is answered `ready` at once;
* `exportPhase_withReady`: the export phase of `instGuard (withReady τ)` is `τ`;
* `exportPhase_mono`, `instGuard_mono`, `denIR_mono_on` (refinement on the core modules of a
  component refines it);
* `engine_le_withReady`: an engine instance without a start function is bounded by its
  start-free strategy, ready at once;
* `exportPhase_engine_noStart`, `exportPhase_engine_start`: the export phase of an engine
  instance.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstExport

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Game (liftMove)

variable {E F : Sig.{0}} {R : Type}

/-! ## Ready at once -/

/-- **In `withReady σ`, `inst` is answered `ready` at once.** -/
theorem withReady_second {σ : Strategy E F} {y : Move E (F.withInst R)}
    {rest : List (Move E (F.withInst R))}
    (h : (.inr (.ask none) :: y :: rest : List (Move E (F.withInst R))) ∈ withReady σ) :
    y = .inr (.ans (m := none) InstAns.ready) := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨y', hy⟩ := Strategy.mem_ofHandler.1 ht
  cases hz with
  | sync b hz =>
    obtain ⟨_, he, -⟩ := handler_run_idle_cons hy
    cases he
  | right c hz =>
    obtain ⟨q', he, hy⟩ := handler_run_idle_cons hy
    cases he
    change (Handler.toReduction (readyH F R)).toLTS.Run (.run none (.pure InstAns.ready)) _ _
      at hy
    cases hz with
    | left a hz =>
      obtain ⟨_, hp⟩ := σ.legal hs
      cases hp with
      | cons hst _ => cases hst
    | right c hz =>
      obtain ⟨he, -⟩ := handler_run_pure_cons hy
      cases he
      rfl
    | sync b hz =>
      obtain ⟨he, -⟩ := handler_run_pure_cons hy
      cases he

/-- In `withReady σ`, a successful instantiation makes no import call. -/
theorem instPlay_withReady {σ : Strategy E F} {cs : List (Σ m : E.Op, E.Ar m)}
    {rest : List (Move E (F.withInst R))}
    (h : instPlay (F := F) cs .ready ++ rest ∈ withReady σ) : cs = [] := by
  rcases cs with _ | ⟨c, cs⟩
  · rfl
  · simp only [instPlay, List.flatMap_cons, List.cons_append] at h
    cases withReady_second h

theorem instPlay_nil (a : InstAns R) (p : List (Move E (F.withInst R))) :
    instPlay (F := F) ([] : List (Σ m : E.Op, E.Ar m)) a ++ p = askInst :: ansInst a :: p := rfl

/-- **The export phase of `instGuard (withReady τ)` is `τ`.** -/
theorem exportPhase_withReady (τ : Strategy E F) :
    exportPhase (instGuard (withReady (R := R) τ)) = τ := by
  refine le_antisymm (Strategy.generate_le ?_) fun p hp => ?_
  · rintro p ⟨cs, hcs⟩ -
    have hw := instGuard_le _ hcs
    obtain rfl := instPlay_withReady hw
    rw [instPlay_nil] at hw
    exact (mem_withReady_iff τ p).1 hw
  · refine Strategy.subset_generate ⟨[], ?_⟩ (τ.legal hp)
    rw [instPlay_nil]
    exact (afterReady_instGuard _ p).2 ((mem_withReady_iff τ p).2 hp)

/-! ## Monotonicity -/

theorem exportPhase_mono {σ σ' : Strategy E (F.withInst R)} (h : σ ≤ σ') :
    exportPhase σ ≤ exportPhase σ' :=
  Strategy.generate_mono fun _ ⟨cs, hcs⟩ => ⟨cs, h hcs⟩

theorem instGuard_mono {σ σ' : Strategy E (F.withInst R)} (h : σ ≤ σ') :
    instGuard σ ≤ instGuard σ' :=
  Strategy.generate_mono fun _ hp => ⟨h hp.1, hp.2⟩

variable {M : Type} [CoreModule M]

mutual
theorem denIR_mono_on {C C' : CoreSemI M} {P : M → Prop} (h : ∀ m, P m → C.sem m ≤ C'.sem m) :
    ∀ c : Comp M, c.AllCore P → c.denIR C ≤ c.denIR C'
  | .mk I ns xs, hc => by
    simp only [Comp.denIR]
    simp only [Comp.AllCore] at hc
    exact Strategy.comp_mono (denNodesI_mono_on h I.length ns hc le_rfl) le_rfl

theorem denNodesI_mono_on {C C' : CoreSemI M} {P : M → Prop}
    (h : ∀ m, P m → C.sem m ≤ C'.sem m) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)), nodesAllCore P ns → ∀ {D D' : Strategy X sigUI}, D ≤ D' →
      denNodesI C e ns D ≤ denNodesI C' e ns D'
  | _, [], _, _, _, hD => by simpa only [denNodesI] using hD
  | e, n :: ns, hns, _, _, hD => by
    simp only [nodesAllCore] at hns
    simp only [denNodesI]
    exact denNodesI_mono_on h _ ns hns.2
      (extI_mono e hD (nodeDenI_mono_on h e n hns.1))

theorem nodeDenI_mono_on {C C' : CoreSemI M} {P : M → Prop}
    (h : ∀ m, P m → C.sem m ≤ C'.sem m) :
    ∀ (e : Nat) (n : Node M), n.AllCore P → n.denI C e ≤ n.denI C' e
  | e, .core m args, hn => by
    simp only [Node.AllCore] at hn
    simp only [Node.denI, coreNodeI]
    exact Strategy.comp_mono le_rfl (Strategy.comp_mono (h m hn) le_rfl)
  | e, .inst c args, hn => by
    simp only [Node.AllCore] at hn
    simp only [Node.denI]
    exact Strategy.comp_mono le_rfl (denIR_mono_on h c hn)
end

/-- **On components whose core modules are bounded by start-free ones ready at once, the export
phase is bounded by the start-free denotation.** -/
theorem denX_le_denU {C : CoreSemI M} {C' : CoreSem M} {P : M → Prop}
    (h : ∀ m, P m → C.sem m ≤ C'.toI.sem m) {c : Comp M} (hc : c.AllCore P) :
    c.denX C ≤ c.denU C' := by
  have h₁ : c.denX C ≤ exportPhase (instGuard (withReady (R := Unit) (c.denU C'))) := by
    rw [← denIR_toI]
    exact exportPhase_mono (instGuard_mono (denIR_mono_on h c hc))
  rwa [exportPhase_withReady] at h₁

/-- For start-free core semantics the export phase is the start-free denotation. -/
theorem denX_toI (C : CoreSem M) (c : Comp M) : c.denX C.toI = c.denU C := by
  rw [Comp.denX, Comp.denI, denIR_toI, exportPhase_withReady]

/-! ## Engine instances -/

variable {En : Engine} {I : Option (IInstance En)} {imps exps : CoreIface}

/-- **An engine instance without a start function is bounded by its start-free strategy, ready
at once.** -/
theorem engine_le_withReady {J : IInstance En} (hI : I = some J) (ha : J.start = none) :
    engineStrategyI En I imps exps ≤ withReady (engineStrategy En J.toE imps exps) := by
  have hJ : addrsOf I = J.addrs := by rw [hI]; rfl
  refine Strategy.ofLTS_le_iff.2 fun s ⟨z, hz⟩ hl => ?_
  rcases run_cases hz with ⟨rfl, -⟩ | ⟨y, hs, -⟩ | ⟨o, l, y, rfl, hs, hr⟩
  · exact Strategy.nil_mem _
  · cases hs
  · cases hs with
    | start hI' ha' => rw [hI] at hI'; cases hI'; rw [ha] at ha'; cases ha'
    | noInst hI' => rw [hI] at hI'; cases hI'
    | noStart hI' ha' =>
      rw [hI] at hI'
      cases hI'
      have h₀ : askInst :: ansInst .ready :: ([] : List (Move (sigN imps.length)
          (sigN exps.length))).map liftMove ∈ withReady (R := Unit)
          (engineStrategy En J.toE imps exps) :=
        (mem_withReady_iff _ []).2 (Strategy.nil_mem _)
      rcases run_readying_inv hr with rfl | ⟨rest, rfl, hr'⟩
      · exact Strategy.of_prefix _ h₀ ⟨[ansInst .ready], rfl⟩
      · obtain ⟨p, y', rfl, -, hy⟩ := run_ready_inv J.store _ hr'
        rw [hJ] at hy
        obtain ⟨_, hpath⟩ := hl
        obtain ⟨x, hx, hx'⟩ := Path.of_append (s := [askInst, ansInst .ready]) hpath
        obtain rfl := Path.det hx (Silmaril.Proofs.Wasm.Component.InstSem.path_round
          (instRound (F := sigN exps.length) (X := sigN imps.length) (R := Unit) [] .ready))
        exact (mem_withReady_iff _ p).2
          (Strategy.mem_ofLTS_of_mem_traces ⟨y', hy⟩ (legal_of_lift ⟨_, hx'⟩))

/-- **The export phase of an engine instance without a start function** is its start-free
strategy. -/
theorem exportPhase_engine_noStart {J : IInstance En} (hI : I = some J) (ha : J.start = none) :
    exportPhase (engineStrategyI En I imps exps) = engineStrategy En J.toE imps exps := by
  refine le_antisymm (Strategy.generate_le ?_) fun p hp => ?_
  · rintro p ⟨cs, hcs⟩ -
    exact ((engine_after_noStart_iff hI ha cs p).1 hcs).2
  · exact Strategy.subset_generate ⟨[], (engine_after_noStart_iff hI ha [] p).2 ⟨rfl, hp⟩⟩
      ((engineStrategy En J.toE imps exps).legal hp)

/-- **The export phase of an engine instance with a start function**: generated by the plays
of `engineStrategy` from every store a start run (with any import calls, answered by the
environment) returns at. -/
theorem exportPhase_engine_start {J : IInstance En} {a : En.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) :
    exportPhase (engineStrategyI En I imps exps) = Strategy.generate {p | ∃ cs c' ys,
      StartRunI En imps (J.store, En.invoke a []) cs c' ∧
        En.status c'.1 c'.2 = .returned (.values ys) ∧
        p ∈ engineStrategy En ⟨c'.1, J.addrs⟩ imps exps} := by
  unfold exportPhase
  congr 1
  ext p
  constructor
  · rintro ⟨cs, h⟩
    obtain ⟨c', ys, hr, hf, hp⟩ := (engine_after_start_iff hI ha cs p).1 h
    exact ⟨cs, c', ys, hr, hf, hp⟩
  · rintro ⟨cs, c', ys, hr, hf, hp⟩
    exact ⟨cs, (engine_after_start_iff hI ha cs p).2 ⟨c', ys, hr, hf, hp⟩⟩

/-- **Without an instance, the export phase never answers.** -/
theorem exportPhase_engine_noInst (hI : I = none) :
    exportPhase (engineStrategyI En I imps exps) = ⊥ := by
  rw [Strategy.bot_eq_generate]
  unfold exportPhase
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  exact fun cs => engine_noInst_not_ready hI cs p

end Silmaril.Proofs.Wasm.Component.InstExport
