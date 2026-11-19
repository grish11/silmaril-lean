module

public import Silmaril.Semantics.Accept.Mixed.Stream.Defs
public import Silmaril.Semantics.Accept.Mixed.Thms
import Silmaril.Proofs.Semantics.Accept.Mixed.Stream.Basic

/-!
# Streaming mixed sessions: laws

* `pstep_acc`: outside undefined behaviour a parsing step moves the append buffer by `accStep`,
  and `pending_eq_foldl`: `Silmaril.Accept.Parse.pending` is the iterated `accStep`;
* `streamRetFrom_at`: `StreamRetFrom … acc t` read at a decomposition `t = u ++ .p e :: v`
  constrains the returns of `e` from every parsing state whose buffer is the pending buffer of
  the parsing events of `u`;
* **streaming assume/guarantee** (`mixedRel_subset_of_streamAG`,
  `mixedFixedRel_subset_of_streamAG`): if in every trace of `T` the writes agreeing with `σ`
  guarantee that the returns are related in `σ` **along the trace** (`StreamReturnsIn`), the
  relation is in `R` (store semantics without undefined behaviour; fixed environments for every
  writer policy). Unlike `mixedRel_subset_of_AG`, `done() -> h` may be constrained by the
  values appended since the last `done`.
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse

universe u

variable {Op V H X : Type u}

theorem pending_eq_foldl (clears : Bool) (acc : List V) (t : List (PEv V H)) :
    pending clears acc t = t.foldl (accStep clears) acc :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Stream.pending_eq_foldl clears acc t

theorem streamRetFrom_at {ppol : PPolicy H} {σ : Env H X} {R : Set (List V × X)} {acc : List V}
    {u : List (MEv Op V H)} {e : PEv V H} {v : List (MEv Op V H)}
    (hS : StreamRetFrom ppol σ R acc (u ++ .p e :: v)) {ps : PState V} {w : List V} {h : H}
    {ps' : PState V} (hps : ps.acc = pending ppol.doneClears acc (parseEvents u))
    (hR : Returns ppol ps e w h ps') (hh : h ≠ ppol.sentinel) {x : X} (hx : σ h = some x) :
    (w, x) ∈ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Stream.streamRetFrom_at hS ps w h ps' hps hR hh x hx

variable [DecidableEq H] {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H}

theorem pstep_acc {σ : Env H X} {s s' : PState V} {e : PEv V H} {A : Set (List V × X)}
    (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) :
    s'.acc = accStep ppol.doneClears s.acc e :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Stream.pstep_acc hs hc

/-- **Streaming assume/guarantee, store semantics.** -/
theorem mixedRel_subset_of_streamAG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → StreamReturnsIn ppol σ R t) :
    mixedRel W pol ppol T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Stream.mixedRel_subset_of_streamAG hw ha hb ho hAG

/-- **Streaming assume/guarantee, fixed environments**, for every writer policy. -/
theorem mixedFixedRel_subset_of_streamAG (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → StreamReturnsIn ppol ρ R t) :
    mixedFixedRel W pol ppol Envs T ⊆ R :=
  Silmaril.Proofs.Semantics.Accept.Mixed.Stream.mixedFixedRel_subset_of_streamAG hb ho hAG

end Silmaril.Accept.Mixed
