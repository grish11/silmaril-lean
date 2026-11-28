module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Environment.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentRegression

/-! # Request-free rows in mixed tables, at the original entries

A mixed table has rows that start with a request and rows that send no
request. No seed is added. Nothing here is inferred from a model.

## The guard

`Ranked row act rank fuel` ranks the edges out of request-free rows, on
rows with their entry Bit. A finite forwarding chain has a ranking. A
silent cycle has none (`spin_not_ranked`); silent cycles are treated
separately below, with a classification in place of the ranking. With a
ranking every action settles within the fuel: it reaches a return or a
request row (`resolveN_settled`). The elimination below is stated for
settled actions.

## Default Paper: the elimination over ranked silent paths

These are equations of arrows of default Paper. They use no opt-in rule.

* `pureRow_const`: a request-free row entered with a constant is the
  action of its exit on that constant.
* `Router.resolved_arrow`: the reusable elimination lemma. Let `sil` give
  the action of each silent state of a router table when entered with the
  Bit `c` assigns to it. If all repeats carry the Bit of their target and
  every action is settled after `n` silent steps, then the table and the
  table with every action resolved have the same entered loop at every
  state. The proof runs the silent states in an inner loop and uses the
  fixpoint and codiagonal laws of iteration, by induction on the fuel.
* `mixWritten_arrow_mixRouter`: the table as written and the table with
  the unused exit of each request-free row rerouted have the same entered
  loops.

## The opt-in quotient: the original entries

* `mixRouter_landed`, `mixWritten_landed`: with a ranking, row `j`
  entered with the constant `q` is `mixLanding row act fuel j q`: a Bit
  returned with no request when the silent path from `(j, q)` reaches a
  return, and otherwise the table of literal request trees entered at the
  request row the path reaches, with the Bit it arrives with. Entries at
  request-free rows are included.
* `mixWritten_eqv_mixCase`: on an arbitrary state, the table entered at
  `j` is its two landings entered by a case on that state.

The steps are the split-state fold of #5273, the elimination above, a
bisimulation that drops the request-free rows no resolved action reaches,
and the specialization of #5277 at the request rows.

## The opt-in quotient: completeness

* `Landed.eqv_iff_rel`: two loops with landings are equal exactly when
  their landings agree at each constant: the same returned Bit, the same
  constant into equal request trees, or silent divergence on both sides.
* `Landed.complete`: exactly when they are valid in every supported
  model. The converse reads the request-prefix model: a return and a
  pending request are told apart, a request shows its query, and literal
  request trees are determined at one constant entry.
* `Pointed.landed`: the loops of the earlier files have landings.
* `mixWritten_complete`, `mixWritten_eqv_ltable_iff_valid`: the instances
  for ranked mixed tables at their original entries.

These depend on phase uniformity, unit η and the request-prefix model.
They are not statements about default Paper.

## Regression

`hopRow` with `hopAct f s` has two request-free rows before a request
row, and a ranking (`hop_ranked`).

* `hop_return`: entered with `true`, two silent hops reach a return.
* `hop_request`: entered with `false`, two silent hops change the Bit and
  reach the request row with `true`.
* `hop_eqv_iff`: two such tables are equal at the first row exactly when
  the hop changes the Bit in the same way and the request row is entered
  with the same Bit.

## Silent cycles: a third landing

* `silent_classification`: every finite table of silent states has a
  closed set `cyc` of states whose silent paths never end, and a fuel
  that resolves every action to a return, a request state or a state of
  `cyc`. The set is chosen classically; for a given table a
  classification is checked by computation.
* `Router.cycle_eqv_spin`: the canonical-cycle lemma, in the opt-in
  quotient. In a router table whose repeats carry the Bit of their
  target, a state of a closed silent set entered with its Bit is the
  canonical silent self-loop `spinRegion`, whatever Bits the cycle
  carries. Two steps. In default Paper, by the roll law and resets, the
  table equals the table whose `cyc` rows are constant rows that repeat
  with `false`. That table is bisimilar to `spinRouter`, which uses the
  phase-uniformity fold.
* `mixWritten_landed3`, `mixWritten_eqv_mixCase3`: a classified mixed
  table entered with each constant lands in a returned Bit, in literal
  request trees, or in `spinRegion`. Original entries and exits are kept.
* `spinRouter_prefixObservations`: in the request-prefix model the
  canonical silent self-loop has no observation, neither a completed run
  nor a pending request. So `Landed.eqv_iff_rel` and `Landed.complete`
  hold with the third landing: silent divergence is separated from an
  immediate return and from a pending labelled request.
* `mixWritten_complete3`: two classified mixed tables are equal at given
  original entries exactly when they are valid in every supported model.

Regression: `flip_landing`, `flip_eqv_spin`, `lead_eqv_flip`: a silent
cycle that negates the Bit, one that keeps it, and a hop into a cycle
are equal. `flip_ne_return`, `flip_ne_request`: the cycle differs from an
immediate return and from every table of literal request trees.
`tri_cycle`, `tri_request`: one request-free row lands in the cycle on
one Bit and at the request row on the other.

## A request followed by silent divergence

`Classified.quiet` requires that no request row repeats into `cyc`. The
landings of this file do not cover a request row whose reply leads into a
silent cycle. `Composite.Silent.Diverge` treats that case for request
rows that are single requests, with tables of labelled rows and canonical
silent rows in place of literal request trees, and states what remains.

## Scope

The request rows are rows of the environment fragment. Nothing is claimed
for packed dispatchers in general, and no completeness is claimed for
default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity


variable {K K₁ K₂ M M' : Nat}

/-! ## The guard -/

/-- With a ranking, the fuel resolves every action. -/
theorem resolveN_settled {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
    {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel) (a : Act (K + (K + 1))) :
    (resolveN (mixSil row act) fuel a).Settled (mixSil row act) :=
  Tables.mix_settled row act hr a

/-- A silent cycle has no ranking. -/
theorem spin_not_ranked (rank : Fin 1 → Bool → Nat) (fuel : Nat) : ¬ Ranked spinRow spinAct rank fuel :=
  Tables.spin_not_ranked rank fuel

/-! ## Default Paper: the elimination over ranked silent paths -/

/-- A request-free row entered with a constant is the action of its exit
on that constant. -/
theorem pureRow_const (M : Nat) (e : Fin 2) (a : Bool → Bool → Act M) (g : Bool) :
    ofRegion (seqValueBranches (const_typed g) (routerRow_typed M (.ret e 0) a)) =
      ofRegion (act_typed M (a (exitBit e) g)) :=
  Tables.pure_const M e a g

/-- A table and the table with every action resolved through its silent
states have the same entered loops, in default Paper. -/
theorem Router.resolved_arrow (t : Router M) (c : Fin (M + 1) → Bool) (sil : Fin (M + 1) → Option (Act M))
    (n : Nat)
    (hsil : ∀ y A, sil y = some A →
      ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) = ofRegion (act_typed M A))
    (hcar : ∀ y A, sil y = some A → A.Carries c) (hact : ∀ x a b, (t.act x a b).Carries c)
    (hset : ∀ x a b, (resolveN sil n (t.act x a b)).Settled sil) (x : Fin (M + 1)) :
    ofRegion ((t.resolved sil n).entered_typed x) = ofRegion (t.entered_typed x) :=
  Tables.silent_entered t c sil n hsil hcar hact hset x

/-- The table as written and the table with the unused exits rerouted
have the same entered loops, in default Paper. -/
theorem mixWritten_arrow_mixRouter (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((mixWritten row act).entered_typed j) = ofRegion ((mixRouter row act).entered_typed j) :=
  Tables.mix_written_arrow row act j

/-! ## The opt-in quotient: the original entries -/

section Entries

variable {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

include hr in
/-- A ranked mixed table entered with each constant is its landing. -/
theorem mixRouter_landed (j : Fin (K + 1)) :
    Landed ((mixRouter row act).entered j) (mixLanding row act fuel j) :=
  Tables.mix_landed row act hr j

include hr in
/-- The same for the table as written. -/
theorem mixWritten_landed (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding row act fuel j) :=
  Tables.written_landed row act hr j

include hr in
/-- On an arbitrary state, the table is its two landings entered by a
case on that state. -/
theorem mixWritten_eqv_mixCase (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase row act fuel j) [Bit] :=
  Tables.written_case row act hr j

end Entries

/-! ## The opt-in quotient: completeness -/

section Complete

variable {r r' : Region signature.Instr} {L : Bool → Landing M} {L' : Bool → Landing M'}

/-- Loops with landings are equal exactly when their landings agree at
each constant. -/
theorem Landed.eqv_iff_rel (hl : Landed r L) (hl' : Landed r' L') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ ∀ q, (L q).Rel (L' q) :=
  Tables.landed_iff_rel h h' hl hl'

/-- And exactly when they are valid in every supported model. -/
theorem Landed.complete (hl : Landed r L) (hl' : Landed r' L') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.landed_complete h h' hl hl'

end Complete

/-- A loop that is literal request trees at each constant lands in them. -/
theorem Pointed.landed {r : Region signature.Instr} {t : Bool → LTable M} {x : Bool → Fin (M + 1)}
    (hp : Pointed r t x) : Landed r fun q => .at (t q) (x q) q :=
  Tables.landed_of_pointed hp

/-- Two ranked mixed tables are equal at given original entries exactly
when they are valid in every supported model. -/
theorem mixWritten_complete {row : Fin (K₁ + 1) → MixRow} {act : Fin (K₁ + 1) → Bool → Bool → Act K₁}
    {rank : Fin (K₁ + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)
    {row' : Fin (K₂ + 1) → MixRow} {act' : Fin (K₂ + 1) → Bool → Bool → Act K₂}
    {rank' : Fin (K₂ + 1) → Bool → Nat} {fuel' : Nat} (hr' : Ranked row' act' rank' fuel')
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  (mixWritten_landed hr i₁).complete (mixWritten_landed hr' i₂) ((mixWritten row act).entered_typed i₁)
    ((mixWritten row' act').entered_typed i₂)

/-- The same against any table of literal request trees. -/
theorem mixWritten_eqv_ltable_iff_valid {row : Fin (K₁ + 1) → MixRow}
    {act : Fin (K₁ + 1) → Bool → Bool → Act K₁} {rank : Fin (K₁ + 1) → Bool → Nat} {fuel : Nat}
    (hr : Ranked row act rank fuel) (s : LTable K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) (s.entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType (s.entered_typed i₂).hasType :=
  (mixWritten_landed hr i₁).complete
    (LTable.pointed_of_eqv (s.entered_typed i₂) s i₂
      (Paper.Extension.Eqv.refl (s.entered_typed i₂).hasType)).landed
    ((mixWritten row act).entered_typed i₁) (s.entered_typed i₂)

/-! ## Regression -/

theorem hop_ranked (l f s : Bool) : Ranked (hopRow l) (hopAct f s) hopRank 3 :=
  Tables.hop_ranked l f s

/-- Entered with `true`, two silent hops reach a return. -/
theorem hop_return (l : Bool) : mixLanding (hopRow l) (hopAct true true) 3 0 true = .ret true :=
  Tables.hop_return l

/-- Entered with `false`, two silent hops change the Bit and reach the
request row with `true`. -/
theorem hop_request (l : Bool) :
    mixLanding (hopRow l) (hopAct true true) 3 0 false =
      .at (mixSource (hopRow l) (hopAct true true) 3) (splitIdx 2 true) true :=
  Tables.hop_request l

/-- Two tables are equal at the first row exactly when the hop changes
the Bit in the same way and the request row is entered with the same Bit. -/
theorem hop_eqv_iff (l f s f' s' : Bool) :
    Eqv false [State] ((mixWritten (hopRow l) (hopAct f s)).entered 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered 0) [Bit] ↔ f = f' ∧ s = s' :=
  Tables.hop_eqv_iff l f s f' s'

/-! ## Silent cycles -/

/-- Every finite table of silent states has a classification. -/
theorem silent_classification (sil : Fin (M + 1) → Option (Act M)) :
    ∃ (cyc : Fin (M + 1) → Bool) (fuel : Nat), Cyclic sil cyc ∧
      ∀ a, (resolveN (cutSil sil cyc) fuel a).Settled (cutSil sil cyc) :=
  Tables.classification sil

/-- A state of a closed silent set, entered with its Bit, is the
canonical silent self-loop. -/
theorem Router.cycle_eqv_spin (t : Router M) (c : Fin (M + 1) → Bool) (cyc : Fin (M + 1) → Bool)
    (nxt : Fin (M + 1) → Fin (M + 1)) (hact : ∀ x a b, (t.act x a b).Carries c)
    (hcyc : ∀ y, cyc y = true →
      ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) =
        ofRegion (act_typed M (.go (nxt y) (c (nxt y)))) ∧ cyc (nxt y) = true)
    (x : Fin (M + 1)) (hx : cyc x = true) :
    Eqv false [(Ty.unit : Ty Empty)] (constEntry (c x) (t.entered x)) spinRegion [Bit] :=
  Tables.cycle_spin_eqv t c cyc nxt hact hcyc x hx

/-- In the request-prefix model the canonical silent self-loop has no
observation. -/
theorem spinRouter_prefixObservations (g : Bool) : spinRouter.prefixObservations 0 g = ∅ :=
  TableModel.spin_obs g

section Cycles

variable {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classified row act cyc fuel)

include hcl in
/-- A classified mixed table entered with each constant is its landing: a
returned Bit, literal request trees, or the canonical silent self-loop. -/
theorem mixWritten_landed3 (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding3 row act cyc fuel j) :=
  Tables.written_landed3 row act hcl j

include hcl in
/-- On an arbitrary state, the table is its two landings entered by a
case on that state. -/
theorem mixWritten_eqv_mixCase3 (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase3 row act cyc fuel j) [Bit] :=
  Tables.written_case3 row act hcl j

end Cycles

/-- Two classified mixed tables are equal at given original entries
exactly when they are valid in every supported model. -/
theorem mixWritten_complete3 {row : Fin (K₁ + 1) → MixRow} {act : Fin (K₁ + 1) → Bool → Bool → Act K₁}
    {cyc : Fin (K₁ + (K₁ + 1) + 1) → Bool} {fuel : Nat} (hcl : Classified row act cyc fuel)
    {row' : Fin (K₂ + 1) → MixRow} {act' : Fin (K₂ + 1) → Bool → Bool → Act K₂}
    {cyc' : Fin (K₂ + (K₂ + 1) + 1) → Bool} {fuel' : Nat} (hcl' : Classified row' act' cyc' fuel')
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  (mixWritten_landed3 hcl i₁).complete (mixWritten_landed3 hcl' i₂) ((mixWritten row act).entered_typed i₁)
    ((mixWritten row' act').entered_typed i₂)

theorem flip_classified : Classified spinRow flipAct allCyc 0 := Tables.flip_classified

/-- A silent cycle that negates the Bit lands in the canonical silent
self-loop at both constants. -/
theorem flip_landing (q : Bool) : mixLanding3 spinRow flipAct allCyc 0 0 q = .spin :=
  Tables.flip_landing q

/-- The cycle that negates the Bit equals the cycle that keeps it. -/
theorem flip_eqv_spin :
    Eqv false [State] ((mixWritten spinRow flipAct).entered 0) ((mixWritten spinRow spinAct).entered 0) [Bit] :=
  Tables.flip_eqv_spin

/-- A hop into a cycle equals the cycle. -/
theorem lead_eqv_flip :
    Eqv false [State] ((mixWritten leadRow leadAct).entered 0) ((mixWritten spinRow flipAct).entered 0) [Bit] :=
  Tables.lead_eqv_flip

/-- The silent cycle is not an immediate return. -/
theorem flip_ne_return :
    ¬ Eqv false [State] ((mixWritten spinRow flipAct).entered 0) ((mixWritten echoRow echoPure).entered 0)
      [Bit] :=
  Tables.flip_ne_return

/-- The silent cycle is not a loop that sends a request. -/
theorem flip_ne_request (s : LTable M) (i : Fin (M + 1)) :
    ¬ Eqv false [State] ((mixWritten spinRow flipAct).entered 0) (s.entered i) [Bit] :=
  Tables.flip_ne_request s i

theorem tri_classified (l : Bool) : Classified (triRow l) triAct triCyc 1 := Tables.tri_classified l

/-- Entered with `false`, the silent path of row zero ends in the cycle. -/
theorem tri_cycle (l : Bool) : mixLanding3 (triRow l) triAct triCyc 1 0 false = .spin :=
  Tables.tri_cycle l

/-- Entered with `true`, it reaches the request row. -/
theorem tri_request (l : Bool) :
    mixLanding3 (triRow l) triAct triCyc 1 0 true =
      .at (mixSource3 (triRow l) triAct triCyc 1) (splitIdx 2 true) true :=
  Tables.tri_request l

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
