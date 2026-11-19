module

public import Silmaril.Semantics.Accept.Mixed.Defs
public import Silmaril.Semantics.Accept.Parse.Thms
import Silmaril.Proofs.Semantics.Accept.Mixed.Basic

/-!
# Mixed sessions: laws

**Relations of trace classes**: `mixedRel` and `mixedFixedRel` are monotone in the traces
(`mixedRel_mono`, `mixedFixedRel_mono`) and preserve unions (`mixedRel_union`,
`mixedFixedRel_union`); `mixedFixedRel` is monotone in the environments
(`mixedFixedRel_mono_envs`).

**Persistence**: stores only grow along mixed runs (`run_store_extends`, across call-local traps
and export calls), so a resolved handle stays resolved to the same tree for every later event
(`run_resolve_stable`): a tree written before a return is the tree every later state agrees on.
Under a fixed environment the store stays below it (`run_fixed_extends`).

**Comparison with parsing sessions** (no undefined behaviour of the writer, no UB on unresolved
handles):

* `mixedRel_subset_parseRel`: the store relation of `T` is included in the parsing relation
  (`Silmaril.Accept.Parse.parseRel`) of its parsing events over the **reachable final stores**
  `reachStores`: a handle resolved in the store current at its return is resolved to the same
  tree in the final store;
* `mixedFixedRel_subset_parseRel`: the fixed-environment relation over `Envs` is included in the
  parsing relation over the same `Envs`.

The inclusions are strict in general: a parsing relation over an environment relates trees the
module never constructed, a mixed relation does not:

* `mixedRel_constructed`: every pair `(w, x)` of the store relation is accepted at a parsing event
  returning a non-sentinel handle `h` for the input `w`, and an **earlier write of the same
  trace returned `h`**;
* `mixedFixedRel_resolves`: over fixed environments, the pair is moreover resolved in some
  `ρ ∈ Envs` that all writes of the trace agree with (`WritesAgree`).

**Assume/guarantee** (`mixedRel_subset_of_AG`, `mixedFixedRel_subset_of_AG`): if in every trace
of `T` the writes agreeing with `σ` guarantee that the returns are related in `σ` (`ReturnsIn`),
for every `σ` (store semantics, no UB) or every `ρ ∈ Envs` (fixed environments), the relation
is included in `R`. In the store semantics the witness `σ` is the final store of the run.
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse

universe u

variable {Op V H X : Type u} [DecidableEq H] {W : Writer Op X} {pol : Policy H}
  {ppol : PPolicy H}

/-! ## Relations of trace classes -/

theorem mixedRel_mono {T T' : Set (List (MEv Op V H))} (h : T ⊆ T') :
    mixedRel W pol ppol T ⊆ mixedRel W pol ppol T' :=
  Host.lang_mono h

theorem mixedRel_union (T T' : Set (List (MEv Op V H))) :
    mixedRel W pol ppol (T ∪ T') = mixedRel W pol ppol T ∪ mixedRel W pol ppol T' :=
  Host.lang_union T T'

theorem mixedFixedRel_mono {Envs : Set (Env H X)} {T T' : Set (List (MEv Op V H))}
    (h : T ⊆ T') : mixedFixedRel W pol ppol Envs T ⊆ mixedFixedRel W pol ppol Envs T' :=
  Set.iUnion_mono fun _ => Host.lang_mono h

theorem mixedFixedRel_union (Envs : Set (Env H X)) (T T' : Set (List (MEv Op V H))) :
    mixedFixedRel W pol ppol Envs (T ∪ T') =
      mixedFixedRel W pol ppol Envs T ∪ mixedFixedRel W pol ppol Envs T' := by
  simp only [mixedFixedRel, langOver, Host.lang_union, Set.iUnion_union_distrib]

theorem mixedFixedRel_mono_envs {Envs Envs' : Set (Env H X)} (h : Envs ⊆ Envs')
    (T : Set (List (MEv Op V H))) :
    mixedFixedRel W pol ppol Envs T ⊆ mixedFixedRel W pol ppol Envs' T := by
  intro q hq
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq ⊢
  obtain ⟨ρ, hq⟩ := hq
  exact ⟨⟨ρ.1, h ρ.2⟩, hq⟩

/-! ## Persistence -/

/-- **Stores only grow** along mixed runs, across call-local traps and export calls. -/
theorem run_store_extends {fix : Option (Env H X)} {s s' : MState V H X}
    {t : List (MEv Op V H)} {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A) :
    s.ws.store.Extends s'.ws.store :=
  Silmaril.Proofs.Semantics.Accept.Mixed.run_extends hr

/-- **A resolved handle stays resolved**: what a return resolves in the current store, it
resolves in every later store of the run. -/
theorem run_resolve_stable {fix : Option (Env H X)} {s s' : MState V H X}
    {t : List (MEv Op V H)} {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A)
    {w : List V} {h : H} {B : Set (List V × X)} (hB : resolve ppol s.ws.store w h = some B) :
    resolve ppol s'.ws.store w h = some B :=
  Silmaril.Proofs.Semantics.Accept.Mixed.resolve_mono (run_store_extends hr) hB

/-- Under a fixed environment the store stays below it. -/
theorem run_fixed_extends {ρ : Env H X} {s s' : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol (some ρ)).Run s t s' A)
    (hρ : s.ws.store.Extends ρ) : s'.ws.store.Extends ρ :=
  Silmaril.Proofs.Semantics.Accept.Mixed.run_fixed hr hρ

/-! ## Comparison with parsing sessions -/

/-- **The store relation is a parsing relation over the reachable final stores.** -/
theorem mixedRel_subset_parseRel (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (T : Set (List (MEv Op V H))) :
    mixedRel W pol ppol T ⊆ parseRel ppol (reachStores W pol ppol T) (parseEvents '' T) :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedRel_subset_parseRel hw ha hb T

/-- **The fixed-environment relation is a parsing relation over the same environments.** -/
theorem mixedFixedRel_subset_parseRel (hb : ppol.onBadHandle ≠ .ub) (Envs : Set (Env H X))
    (T : Set (List (MEv Op V H))) :
    mixedFixedRel W pol ppol Envs T ⊆ parseRel ppol Envs (parseEvents '' T) :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedFixedRel_subset_parseRel hb Envs T

/-- **Pairs are returned, constructed trees**: the returned handle was written earlier in the
same trace. -/
theorem mixedRel_constructed (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {q : List V × X} (hq : q ∈ mixedRel W pol ppol T) :
    ∃ t ∈ T, ∃ u e v, t = u ++ .p e :: v ∧ ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧
      h ≠ ppol.sentinel ∧ ∃ op args, MEv.w (.write op args h) ∈ u :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedRel_constructed hw ha hb ho hq

/-- **Pairs over fixed environments resolve in an environment the writes agree with.** -/
theorem mixedFixedRel_resolves (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))} {q : List V × X}
    (hq : q ∈ mixedFixedRel W pol ppol Envs T) :
    ∃ ρ ∈ Envs, ∃ t ∈ T, WritesAgree W pol.sentinel ρ t ∧ ∃ u e v, t = u ++ .p e :: v ∧
      ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧ h ≠ ppol.sentinel ∧
        ρ h = some q.2 ∧ ∃ op args, MEv.w (.write op args h) ∈ u :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedFixedRel_resolves hb ho hq

/-! ## Assume/guarantee -/

/-- **Assume/guarantee, store semantics**: if in every trace the writes agreeing with any `σ`
guarantee returns related in `σ`, the relation is in `R`. -/
theorem mixedRel_subset_of_AG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → ReturnsIn ppol σ R t) :
    mixedRel W pol ppol T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedRel_subset_of_AG hw ha hb ho hAG

/-- **Assume/guarantee, fixed environments**, for every writer policy. -/
theorem mixedFixedRel_subset_of_AG (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))} {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → ReturnsIn ppol ρ R t) :
    mixedFixedRel W pol ppol Envs T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.mixedFixedRel_subset_of_AG hb ho hAG

end Silmaril.Accept.Mixed
