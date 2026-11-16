module

public import Silmaril.Games.Abstract.SessionIter3.Defs
public import Silmaril.Games.Abstract.SessionIter2.Thms
import Silmaril.Proofs.Games.Abstract.SessionIter3.Iter
import Silmaril.Proofs.Games.Abstract.SessionIter3.Plays

/-!
# Session iteration of total bodies: call prefixes and pending plays (theorems)

`SessionIter2.mem_satP_iterS` describes the call prefixes of `iterS t` for an admissible body.
Here the body is only total (`StratOps.Total`: some observation at every store and argument).

**Iteration of triples** (proofs in `Silmaril.Proofs.Games.Abstract.SessionIter3.Iter`):

* `exists_contChain_of_satP_iterT`, with no hypothesis: a call prefix of `iterT T` is a finite
  chain of continuing iterations (`FullFun.ContChain`) followed by a call prefix of the body. A
  call prefix inside the log of an (infinite) continuing chain is a call prefix of the
  continuing return it falls in;
* `total_iterT`: **iteration preserves totality**. This is a dependent-choice argument: at a
  point where `iterT T` has no observation, `T` can only return continuing to such a point, so
  these returns chain forever. Their logs are eventually empty (a spin divergence of `iterT T`)
  or infinitely often nonempty (a productive stream of `iterT T`), a contradiction either way;
* `mem_satP_iterT_of_total`: for a total body, the converse holds. A call prefix forced by a
  continuing return of the body is extended by an observation of `iterT T` (which is total) at
  the point it continues to.

**Session iteration** (proofs in `…SessionIter3.Plays`), through `iterS t = iterT (mapT t
iterAssoc)`:

* `satP_iterS_subset`, with no hypothesis: `satP (iterS t) s a ⊆ contSatP t s a`;
* `total_iterS`, `mem_satP_iterS_of_total`, `satP_iterS_of_total`: for a total body,
  `satP (iterS t) = contSatP t`: finitely many continuing iterations (`ContS`), then a call
  prefix of the body. The hypothesis is needed: a call prefix forced only by a continuing return
  to a point with no observation is not a call prefix of `iterS t`;
* `mem_pending_iterS_of_total`: the pending plays of `threadS (iterS t) s₀` for a total body,
  by `StratSession.mem_pending` and `SessionIter.rounds_iterS`.
-/

public section

namespace Silmaril.Games.Abstract.SessionIter3

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionIter Silmaril.Games.Abstract.SessionIter2

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Iteration of triples -/

section IterT

variable {T : ObsTriple E S A (B ⊕ A)}

/-- **Call prefixes of an iteration**, one inclusion, with no hypothesis: finitely many
continuing iterations, then a call prefix of the body. -/
theorem exists_contChain_of_satP_iterT {s : S} {a : A} {c : List (Call E)} {m : E.Op}
    (h : (c, m) ∈ satP (iterT T) s a) :
    ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
      c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.exists_contChain_of_satP_iterT h

/-- **Iteration preserves totality.** -/
theorem total_iterT (hT : Total T) : Total (iterT T) :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.total_iterT hT

/-- **Call prefixes of an iteration of a total body**: finitely many continuing iterations,
then a call prefix of the body. -/
theorem mem_satP_iterT_of_total (hT : Total T) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (iterT T) s a ↔
      ∃ c₁ s' a' c₂, FullFun.ContChain T.1 s a c₁ s' a' ∧ (c₂, m) ∈ satP T s' a' ∧
        c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.mem_satP_iterT_of_total hT

end IterT

/-! ## Session iteration -/

section Iter

variable {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}

theorem mem_contSatP {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ contSatP t s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ :=
  Iff.rfl

/-- **Call prefixes of a session iteration**, one inclusion, with no hypothesis. -/
theorem satP_iterS_subset {s : S} {a : A} : satP (iterS t) s a ⊆ contSatP t s a :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.satP_iterS_subset

/-- **Session iteration preserves totality.** -/
theorem total_iterS (ht : Total t) : Total (iterS t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.total_iterS ht

/-- **Call prefixes of a session iteration of a total body**: finitely many continuing
iterations, then a call prefix of the body. -/
theorem mem_satP_iterS_of_total (ht : Total t) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (iterS t) s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.mem_satP_iterS_of_total ht

/-- **Call prefixes of a session iteration of a total body**, as an equation. -/
theorem satP_iterS_of_total (ht : Total t) : satP (iterS t) = contSatP t :=
  Silmaril.Proofs.Games.Abstract.SessionIter3.satP_iterS_of_total ht

/-- **Pending plays of an iterated session** (total body): completed rounds, then finitely many
continuing iterations and a call prefix of the body. -/
theorem mem_pending_iterS_of_total (ht : Total t) {s₀ : S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A} {c : List (Call E)}
    {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
        (threadS (iterS t) s₀).toStrategy ↔
      ∃ s, RoundsBy (IterRet t) s₀ rs s ∧
        ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ := by
  simp only [StratSession.mem_pending, rounds_iterS, mem_satP_iterS_of_total ht]

end Iter

end Silmaril.Games.Abstract.SessionIter3
