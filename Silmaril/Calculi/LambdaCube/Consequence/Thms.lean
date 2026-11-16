module

public import Silmaril.Calculi.LambdaCube.Consequence.Defs
public import Silmaril.Logic.Consequence.Institution.Thms

/-!
# Lambda-cube judgements as consequence systems: laws

* `seq_closed`: semantic consequence of judgements is closed under `Structural.tarskiRules`
  (reflexivity, weakening along `⊆` of the list of *judgements*, multi-cut); hence exchange and
  contraction of judgement premises. This is about the outer list of judgements, never about the
  dependent context inside a judgement.
* `derivableSys_le_seq`: derivable judgements are semantic consequences of anything (the
  `sound` field of `Semantics`).
* `derivableSys_weak`, `derivableSys_cut`: theoremhood weakens and cuts, trivially. Reflexivity
  is **not** claimed: a premise judgement need not be derivable.
* `derivableSys_mono`: theorems of a smaller corner are theorems of a larger one
  (`PTSJudgment.inclusion`).
-/

@[expose] public section

namespace Silmaril.Calculi.LambdaCube

open Silmaril.Consequence

theorem Semantics.seq_closed {c : Corner} (M : Semantics c) :
    Structural.Closed Structural.tarskiRules M.seq :=
  roomSeq_closed M.room

theorem Semantics.seq_exchange {c : Corner} (M : Semantics c) : Structural.Exchange M.seq :=
  Structural.WeakSubset.exchange M.seq_closed.weak

theorem derivableSys_le_seq {c : Corner} (M : Semantics c) : derivableSys c ≤ M.seq :=
  fun _ _ hj m _ => M.sound hj m

theorem derivableSys_weak (c : Corner) : Structural.WeakensAlong (fun _ _ => True) (derivableSys c) :=
  fun _ _ _ _ h => h

theorem derivableSys_cut (c : Corner) : Structural.Cut (derivableSys c) :=
  fun _ _ _ h => h

theorem derivableSys_mono {c d : Corner} (h : c ≤ d) : derivableSys c ≤ derivableSys d :=
  fun _ j hj => PTSJudgment.inclusion (j := j) h hj

end Silmaril.Calculi.LambdaCube
