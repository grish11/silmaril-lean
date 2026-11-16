module

public import Silmaril.Wasm.Abstract.BodyDet.Defs
public import Silmaril.Wasm.Abstract.BodyStrat.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyDet.Basic

/-!
# Deterministic observation triples: theorems

* `toTriple_det`: **the triple of every body is deterministic given
  answers.** A body is an interaction tree: one next event at every node, so
  along one call log there is one node, with at most one pending call and
  never both an end and a call. A `div` end is the silent tree `diverge`,
  which makes no call, so exclusivity holds for all three ends.
* `denL_det`, `toDStratBody_denL_eq`: the same for code, and the play object
  of code is the strategy of a saturated deterministic triple.
* `toDStrat_pdet`: the play object of a saturated deterministic triple has
  at most one Proponent move after each play; hence so has every body's
  (`toDStratBody_pdet`, `toDStratBody_denL_pdet`).
* Cross-log forms for saturated triples: `TripleDet.pend_next` (a pending
  call is the next call of every finished behaviour extending its log), and,
  for productive runs, `TripleDet.inf_pend_next`, `TripleDet.inf_not_fin`,
  `TripleDet.inf_fin_next`, `TripleDet.inf_inf_next`: a productive run agrees
  with pending calls, finished behaviours and other productive runs as long
  as the answers agree. Also `TripleDet.end_unique`: one end per log.

Saturation is needed for the cross-log forms: clauses (b) and (c) of
`TripleDet` say nothing about logs that are not pending, so without it a
finished behaviour could start with a call other than the one pending after
`[]`.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.BodyDet.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.BodyDet

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.BodyStrat

universe u

/-! ## Consequences for triples -/

section Triple

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A B} {s : S} {a : A}

/-- Finished behaviours with the same log have the same end. -/
theorem TripleDet.end_unique (h : TripleDet t) {c : List (Call E)} {e e' : End S B}
    (he : (c, e) ∈ t.1 s a) (he' : (c, e') ∈ t.1 s a) : e = e' :=
  Silmaril.Proofs.Wasm.Abstract.BodyDet.agree_self (h.fin s a _ _ he he')

/-- In a saturated deterministic triple, a pending call is the next call of
every finished behaviour extending its log. -/
theorem TripleDet.pend_next (h : TripleDet t) (hs : StratObs.Saturated t)
    {c d : List (Call E)} {m m' : E.Op} {n : E.Ar m'} {e : End S B}
    (hm : (c, m) ∈ t.2.1 s a) (he : (c ++ ⟨m', n⟩ :: d, e) ∈ t.1 s a) : m = m' :=
  h.pend s a c m m' hm
    (StratObs.saturated_iff.1 hs ▸ .inr (.inr (.inl ⟨_, e, he, n, d, rfl⟩)))

/-- The pending call after a prefix of a productive run is the run's call. -/
theorem TripleDet.inf_pend_next (h : TripleDet t) {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a)
    {k : ℕ} {m : E.Op} (hm : (streamTake ω k, m) ∈ t.2.1 s a) : m = (ω k).1 :=
  h.pend s a _ _ _ hm (h.inf s a ω hω k)

/-- No prefix of a productive run ends a finished behaviour. -/
theorem TripleDet.inf_not_fin (h : TripleDet t) {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a)
    (k : ℕ) (e : End S B) : (streamTake ω k, e) ∉ t.1 s a :=
  fun he => h.excl s a _ e _ he (h.inf s a ω hω k)

/-- In a saturated deterministic triple, a finished behaviour extending a
prefix of a productive run makes the run's next call. -/
theorem TripleDet.inf_fin_next (h : TripleDet t) (hs : StratObs.Saturated t)
    {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a) {k : ℕ} {d : List (Call E)} {m' : E.Op}
    {n : E.Ar m'} {e : End S B} (he : (streamTake ω k ++ ⟨m', n⟩ :: d, e) ∈ t.1 s a) :
    m' = (ω k).1 :=
  (h.pend_next hs (h.inf s a ω hω k) he).symm

/-- Two productive runs with the same first `k` answered calls make the same
next call. -/
theorem TripleDet.inf_inf_next (h : TripleDet t) {ω ω' : ℕ → Call E} (hω : ω ∈ t.2.2 s a)
    (hω' : ω' ∈ t.2.2 s a) {k : ℕ} (hk : streamTake ω k = streamTake ω' k) :
    (ω k).1 = (ω' k).1 :=
  h.pend s a _ _ _ (h.inf s a ω hω k) (hk ▸ h.inf s a ω' hω' k)

/-- **The play object of a saturated deterministic triple has at most one
Proponent move after each play.** -/
theorem toDStrat_pdet (hs : StratObs.Saturated t) (hd : TripleDet t) :
    PDet (StratObs.toDStrat t).toStrategy :=
  Silmaril.Proofs.Wasm.Abstract.BodyDet.toDStrat_pdet hs hd

end Triple

/-! ## Bodies -/

section Body

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-- **The triple of a body is deterministic given answers.** -/
theorem toTriple_det (f : Hom E S T A B) : TripleDet (toTriple f) :=
  Silmaril.Proofs.Wasm.Abstract.BodyDet.toTriple_det f

/-- The play object of a body is the strategy of a saturated deterministic
triple. -/
theorem toDStratBody_eq (f : Hom E S T A B) :
    ∃ t, StratObs.Saturated t ∧ TripleDet t ∧ toDStratBody f = StratObs.toDStrat t :=
  ⟨_, toTriple_saturated f, toTriple_det f, rfl⟩

/-- The play object of a body has at most one Proponent move after each play. -/
theorem toDStratBody_pdet (f : Hom E S T A B) : PDet (toDStratBody f).toStrategy :=
  toDStrat_pdet (toTriple_saturated f) (toTriple_det f)

end Body

open Silmaril.Wasm.Binaryen Silmaril.Wasm.Abstract.ExposePStruct

/-- The triple of code is deterministic given answers. -/
theorem denL_det {H : Type} (es : List BExpr) : TripleDet (toTriple (denL (H := H) es)) :=
  toTriple_det _

/-- The play object of code is the strategy of a saturated deterministic
triple. -/
theorem toDStratBody_denL_eq {H : Type} (es : List BExpr) :
    ∃ t, StratObs.Saturated t ∧ TripleDet t ∧
      toDStratBody (denL (H := H) es) = StratObs.toDStrat t :=
  toDStratBody_eq _

/-- The play object of code has at most one Proponent move after each play. -/
theorem toDStratBody_denL_pdet {H : Type} (es : List BExpr) :
    PDet (toDStratBody (denL (H := H) es)).toStrategy :=
  toDStratBody_pdet _

end Silmaril.Wasm.Abstract.BodyDet
