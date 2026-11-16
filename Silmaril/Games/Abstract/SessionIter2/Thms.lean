module

public import Silmaril.Games.Abstract.SessionIter2.Defs
public import Silmaril.Games.Abstract.SessionIter.Thms
import Silmaril.Proofs.Games.Abstract.SessionIter2.Det
import Silmaril.Proofs.Games.Abstract.SessionIter2.Frame
import Silmaril.Proofs.Games.Abstract.SessionIter2.Plays

/-!
# Session iteration: plays of sequenced and iterated sessions, determinism, strength (theorems)

**Components** (proofs in `Silmaril.Proofs.Games.Abstract.SessionIter2.Plays`). The divergent
behaviours, productive streams and call prefixes (`satP`) of `seqS t u` and `iterS t`, in terms
of `t` and `u`:

* `mem_seqS_div`, `mem_seqS_inf`: `t` diverges (has a stream), or returns a value and then `u`
  diverges (has a stream), the logs concatenated; a continuing trap of `t` adds nothing;
* `mem_satP_seqS` (for a total `u`, `StratOps.Total`) and `mem_satP_seqS_of_adm` (for an
  admissible `t`): a call prefix of `t`, or a value of `t` and a call prefix of `u`. Some
  hypothesis is needed: a call prefix forced only by a value return of `t` is lost when `u` has
  no observation after it (`StratOps.not_sat_seqT`);
* `mem_iterS_div`: finitely many continuing iterations (`ContS`), then the body diverges or an
  infinite chain of *silent* continuing iterations starts (`InfContS t s a fun _ => []`);
* `mem_iterS_inf`: finitely many continuing iterations then a stream of the body, or an infinite
  chain of continuing iterations (`InfContS`) whose logs concatenate to the stream
  (`Shape.StreamConcat`, so infinitely many of them call);
* `mem_satP_iterS` (for an admissible body): finitely many continuing iterations, then a call
  prefix of the body.

**Session plays.** After completed session rounds (`RoundsBy (SeqRet t u)`, `RoundsBy (IterRet t)`,
from `SessionIter.rounds_seqS`, `rounds_iterS`), the pending plays (`mem_pending_seqS`,
`mem_pending_seqS_of_adm`, `mem_pending_iterS`), divergent plays (`mem_div_seqS`, `mem_div_iterS`,
no hypothesis) and infinite plays (`mem_inf_seqS`, `mem_inf_iterS`, for components deterministic
given answers) of `threadS (seqS t u) s₀` and `threadS (iterS t) s₀` are those components, by
`StratSession.mem_pending`, `mem_div_iff` and `mem_inf_iff_of_det`.

**Determinism** (proof in `…SessionIter2.Det`). `det_seqS`: session sequencing preserves
determinism given answers (`AFun.Det`), with no further hypothesis. Sequencing hides no calls,
so the obstruction for linking (`SessionLinkCex.not_det_linkS_may`: a hidden call to a diverging
server makes a return and a divergence with the same log) does not arise: two behaviours of
`seqS t u` agree on their `t`-parts, and when those end alike, in the same value and store, on
their `u`-parts.

**Store strength** (proofs in `…SessionIter2.Frame`). `frameS_iterT`, `frameS_iterS`: store
strength commutes with iteration, on the nose. A framed body leaves the second store component
untouched, so its finite behaviours, continuing chains and infinite continuing chains from
`(s, s')` are those of the body from `s` with `s'` attached.
-/

public section

namespace Silmaril.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionIter

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-! ## Determinism -/

/-- **Session sequencing preserves determinism given answers.** -/
theorem det_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : AFun.Det t.1) (hu : AFun.Det u.1) :
    AFun.Det (seqS t u).1 :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.det_seqS ht hu

/-! ## Components of a sequence -/

section Seq

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})}

/-- **Divergences of a sequence**: `t` diverges, or returns a value and `u` diverges. -/
theorem mem_seqS_div {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (seqS t u).1 s a ↔ (c, End.div) ∈ t.1 s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, End.div) ∈ u.1 s₁ b ∧
        c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_seqS_div

/-- **Productive streams of a sequence**: a stream of `t`, or a value of `t` then a stream
of `u`. -/
theorem mem_seqS_inf {s : S} {a : A} {ω : ℕ → Call E} :
    ω ∈ (seqS t u).2.2 s a ↔ ω ∈ t.2.2 s a ∨
      ∃ c b s₁ ω', (c, End.ret (.inl b) s₁) ∈ t.1 s a ∧ ω' ∈ u.2.2 s₁ b ∧ ω = c ++ₛ ω' :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_seqS_inf

/-- **Call prefixes of a sequence** with a total second part: a call prefix of `t`, or a value
of `t` then a call prefix of `u`. -/
theorem mem_satP_seqS (hu : Total u) {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ satP (seqS t u) s a ↔ (c, m) ∈ satP t s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
        c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_satP_seqS hu

/-- **Call prefixes of a sequence** with an admissible first part. -/
theorem mem_satP_seqS_of_adm (ht : Admissible t) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (seqS t u) s a ↔ (c, m) ∈ satP t s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
        c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_satP_seqS_of_adm ht

/-! ## Plays of a sequenced session -/

variable {s₀ : S}

/-- **Pending plays of a sequenced session** (total `u`): completed rounds, then a call prefix of
`t`, or a value of `t` and a call prefix of `u`. -/
theorem mem_pending_seqS (hu : Total u) {rs : List (A × List (Call E) × (C ⊕ PUnit.{u + 1}))}
    {a : A} {c : List (Call E)} {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
        (threadS (seqS t u) s₀).toStrategy ↔
      ∃ s, RoundsBy (SeqRet t u) s₀ rs s ∧ ((c, m) ∈ satP t s a ∨
        ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
          c = c₁ ++ c₂) := by
  simp only [StratSession.mem_pending, rounds_seqS, mem_satP_seqS hu]

/-- **Pending plays of a sequenced session** (admissible `t`). -/
theorem mem_pending_seqS_of_adm (ht : Admissible t)
    {rs : List (A × List (Call E) × (C ⊕ PUnit.{u + 1}))} {a : A} {c : List (Call E)}
    {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
        (threadS (seqS t u) s₀).toStrategy ↔
      ∃ s, RoundsBy (SeqRet t u) s₀ rs s ∧ ((c, m) ∈ satP t s a ∨
        ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
          c = c₁ ++ c₂) := by
  simp only [StratSession.mem_pending, rounds_seqS, mem_satP_seqS_of_adm ht]

/-- **Divergent plays of a sequenced session**: completed rounds, then `t` diverges, or returns a
value and `u` diverges. -/
theorem mem_div_seqS {p : List (Move E (sig1 A C))} :
    p ∈ (threadS (seqS t u) s₀).div ↔ ∃ rs s a c, RoundsBy (SeqRet t u) s₀ rs s ∧
      ((c, End.div) ∈ t.1 s a ∨ ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧
        (c₂, End.div) ∈ u.1 s₁ b ∧ c = c₁ ++ c₂) ∧
      p = sroundsMoves rs ++ .inr (.ask a) :: callMoves c := by
  simp only [StratSession.mem_div_iff, rounds_seqS, mem_seqS_div]

/-- **Infinite plays of a sequenced session** (components deterministic given answers): completed
rounds, then a stream of `t` or a value of `t` and a stream of `u`; or a coherent infinite
sequence of `SeqRet` rounds. -/
theorem mem_inf_seqS (ht : AFun.Det t.1) (hu : AFun.Det u.1)
    {I : Set (List (Move E (sig1 A C)))} :
    I ∈ (threadS (seqS t u) s₀).inf ↔
      (∃ rs s a ω, RoundsBy (SeqRet t u) s₀ rs s ∧ (ω ∈ t.2.2 s a ∨
        ∃ c b s₁ ω', (c, End.ret (.inl b) s₁) ∈ t.1 s a ∧ ω' ∈ u.2.2 s₁ b ∧ ω = c ++ₛ ω') ∧
          I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ (a : ℕ → A) (r : ℕ → List (Call E) × (C ⊕ PUnit.{u + 1})) (s : ℕ → S),
        (s 0 = s₀ ∧ ∀ k, SeqRet t u (s k) (a k) (r k).1 (r k).2 (s (k + 1))) ∧
        I = sroundsPlay a r := by
  simp only [mem_inf_iff_of_det (det_seqS ht hu), rounds_seqS, mem_seqS_inf,
    Silmaril.Proofs.Games.Abstract.SessionIter2.infRounds_iff, mem_seqS_ret]

end Seq

/-! ## Components of an iteration -/

section Iter

variable {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}

/-- **Divergences of an iteration**: finitely many continuing iterations, then the body
diverges, or an infinite chain of silent continuing iterations. -/
theorem mem_iterS_div {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (iterS t).1 s a ↔ ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧
      ((c₂, End.div) ∈ t.1 s' a' ∨ (c₂ = [] ∧ InfContS t s' a' fun _ => [])) ∧
        c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_iterS_div

/-- **Productive streams of an iteration**: finitely many continuing iterations then a stream of
the body, or an infinite chain of continuing iterations whose logs make up the stream. -/
theorem mem_iterS_inf {s : S} {a : A} {ω : ℕ → Call E} :
    ω ∈ (iterS t).2.2 s a ↔
      (∃ c s' a' ω', ContS t s a c s' a' ∧ ω' ∈ t.2.2 s' a' ∧ ω = c ++ₛ ω') ∨
        ∃ l, InfContS t s a l ∧ Shape.StreamConcat l ω :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_iterS_inf

/-- **Call prefixes of an iteration** of an admissible body: finitely many continuing
iterations, then a call prefix of the body. -/
theorem mem_satP_iterS (ht : Admissible t) {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ satP (iterS t) s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.mem_satP_iterS ht

/-! ## Plays of an iterated session -/

variable {s₀ : S}

/-- **Pending plays of an iterated session** (admissible body): completed rounds, then finitely
many continuing iterations and a call prefix of the body. -/
theorem mem_pending_iterS (ht : Admissible t)
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A} {c : List (Call E)}
    {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
        (threadS (iterS t) s₀).toStrategy ↔
      ∃ s, RoundsBy (IterRet t) s₀ rs s ∧
        ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ := by
  simp only [StratSession.mem_pending, rounds_iterS, mem_satP_iterS ht]

/-- **Divergent plays of an iterated session**: completed rounds, then finitely many continuing
iterations and a divergence of the body or an infinite silent chain of continuing iterations. -/
theorem mem_div_iterS {p : List (Move E (sig1 A B))} :
    p ∈ (threadS (iterS t) s₀).div ↔ ∃ rs s a c, RoundsBy (IterRet t) s₀ rs s ∧
      (∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧
        ((c₂, End.div) ∈ t.1 s' a' ∨ (c₂ = [] ∧ InfContS t s' a' fun _ => [])) ∧
          c = c₁ ++ c₂) ∧
      p = sroundsMoves rs ++ .inr (.ask a) :: callMoves c := by
  simp only [StratSession.mem_div_iff, rounds_iterS, mem_iterS_div]

/-- **Infinite plays of an iterated session** (body deterministic given answers): completed
rounds, then finitely many continuing iterations and a stream of the body, or an infinite chain
of continuing iterations with infinitely many calls; or a coherent infinite sequence of
`IterRet` rounds. -/
theorem mem_inf_iterS (ht : AFun.Det t.1) {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadS (iterS t) s₀).inf ↔
      (∃ rs s a ω, RoundsBy (IterRet t) s₀ rs s ∧
        ((∃ c s' a' ω', ContS t s a c s' a' ∧ ω' ∈ t.2.2 s' a' ∧ ω = c ++ₛ ω') ∨
          ∃ l, InfContS t s a l ∧ Shape.StreamConcat l ω) ∧
          I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ (a : ℕ → A) (r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})) (s : ℕ → S),
        (s 0 = s₀ ∧ ∀ k, IterRet t (s k) (a k) (r k).1 (r k).2 (s (k + 1))) ∧
        I = sroundsPlay a r := by
  simp only [mem_inf_iff_of_det (det_iterS ht), rounds_iterS, mem_iterS_inf,
    Silmaril.Proofs.Games.Abstract.SessionIter2.infRounds_iff, mem_iterS_ret]
  exact Iff.rfl

end Iter

/-! ## Store strength -/

/-- **Store strength commutes with iteration of triples.** -/
theorem frameS_iterT {S' : Type u} (t : ObsTriple E S A (B ⊕ A)) :
    frameS S' (iterT t) = iterT (frameS S' t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.frameS_iterT t

/-- **Store strength commutes with session iteration.** -/
theorem frameS_iterS {S' : Type u} (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    frameS S' (iterS t) = iterS (frameS S' t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.frameS_iterS t

end Silmaril.Games.Abstract.SessionIter2
