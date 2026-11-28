module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomBranching
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomRenaming

/-! # Completeness for case trees on tagged tuple replies

The ordered trace interpretation whose atoms are natural numbers reflects
native equality of branching operands. This is proved, not assumed.

A reply carries one of finitely many ordered tags, and each tag has its
own ordered tuple of atoms. A request binds the reply, cases on it tag by
tag in order, and unpacks the tuple of the chosen tag into atom slots in
order. The exits are an ordered list of types, and a leaf returns a
payload assembled from the atom slots in scope at one exit of the type of
the payload.

At an environment that gives distinct tokens to the atom slots, two case
trees with the same ordered traces are the same term. The induction
follows the tree.

- A leaf is determined by the value it returns: the value fixes the exit
  position, the exit type and the payload value, and at distinct tokens
  the payload value fixes the payload tree.
- A request is determined by its first logged event, which records the
  primitive and the tokens of the argument. Every reply value is
  possible, so the run of the request contains the run of its
  continuation at every reply.
- A case split on the bound reply runs the arm of the tag of the reply.
  The two arms are compared at the replies of their own tags.
- A tuple is compared at consecutive unused tokens. Unpacking binds its
  first atom at the next token and continues with the rest. Every newly
  bound atom slot gets a token that no older slot has.

Slots that hold a bound reply or a tuple of two or more atoms are not
atom slots. They stay in scope and do not affect the separation.

A ranked sentence between entries whose emitted operands are natively
equal to case trees, over a separable bound context, is therefore valid in
all supported models exactly when the emitted operands are natively equal.
The sentence is at the original ordered exits of the entries. On the
graphs read back from two case trees, validity is equality of the trees,
and so is equality of their ordered-exit arrows at the one model.

The class is exact. A reply has at least one tag and each tag carries a
flat ordered tuple of atoms. Every request is followed at once by the
full case split and unpacking of its reply. Each leaf returns one
assembled payload at one exit of its type. Reply payloads with nested
products or sums, cases on other scrutinees, partial or reordered
unpacking, and returned payloads that contain sums are outside it.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ run traceArrow)
open LetSeq.StraightLine.Structural (Assembly Separates)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## Separating environments -/

/-- A separating environment extends by the next unused token at a new
atom slot. -/
theorem separates_fresh {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β} {k : Nat}
    (sep : Separates ρ (Set.Iio k)) (a : α) :
    Separates (ρ.snoc (A := Ty.base a) (k : Nat)) (Set.Iio (k + 1)) :=
  separates_fresh_proof sep a

/-- A context of older atom captures is separable. -/
theorem separable_atoms (atoms : AtomContext β) : Separable β :=
  separable_atoms_proof atoms

/-- A separable context stays separable under a new atom slot. -/
theorem separable_snoc (separable : Separable β) (a : α) : Separable (β.snoc (.base a)) :=
  let ⟨ρ, k, sep⟩ := separable
  ⟨ρ.snoc (A := Ty.base a) (k : Nat), k + 1, separates_fresh sep a⟩

omit [TaggedSignature α Φ] in
/-- A separating environment stays separating under a new slot that is
not an atom: a bound reply, a tuple of two or more atoms, or the unit. -/
theorem separates_other {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β} {used : Set Nat}
    (sep : Separates ρ used) {X : Ty α} (other : ∀ a, X ≠ .base a)
    (x : LetSeq.StraightLine.Structural.Value (α := α) X) : Separates (ρ.snoc x) used :=
  separates_other_proof sep other x

/-! ## The reductions at a request, a case split and a tuple -/

variable {t u : LetCase.LocallyNameless.Tm Empty Φ n}

/-- At a request with the same primitive and argument, the ordered traces
agree exactly when the continuations agree at every reply. The older
slots keep their values. -/
theorem ask_run_eq_iff (f : Φ) (argument : Assembly β (instrSrc f))
    {k k' : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (reply : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k)
    (reply' : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k')
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ask f argument reply).typing ρ = run (CaseTree.ask f argument reply').typing ρ ↔
      ∀ w : LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (replyTags f)),
        run reply.typing (ρ.snoc w) = run reply'.typing (ρ.snoc w) :=
  ask_run_eq_iff_proof f argument reply reply' ρ

/-- A case split on a pending reply runs the arm of the tag of the reply:
the left arm with the tuple of the first tag, or the right arm with the
reply at the remaining tags. -/
theorem run_split (atoms next : List α) (rest : List (List α))
    {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
    (left : CaseTree (.tuple atoms) ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tupleTy atoms)) L l)
    (right : CaseTree (.tags (next :: rest))
      ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tagsTy (next :: rest))) L r)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
    (w : LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (atoms :: next :: rest))) :
    run (CaseTree.split atoms next rest left right).typing (ρ.snoc w) =
      Sum.elim (fun x => run left.typing ((ρ.snoc w).snoc x)) (fun y => run right.typing ((ρ.snoc w).snoc y)) w :=
  run_split_proof atoms next rest left right ρ w

/-- Unpacking a pending tuple of two or more atoms binds its first atom
and the rest, in that order. -/
theorem run_pair (a b : α) (rest : List α) {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
    (later : CaseTree (.tuple (b :: rest))
      (((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L t)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
    (w : LetSeq.StraightLine.Structural.Value (α := α) (tupleTy (a :: b :: rest))) :
    run (CaseTree.pair a b rest later).typing (ρ.snoc w) =
      run later.typing (((ρ.snoc w).snoc (A := Ty.base a) w.1).snoc w.2) :=
  run_pair_proof a b rest later ρ w

/-! ## Exits and payloads -/

omit [TaggedSignature α Φ] in
/-- The value returned at an exit fixes the type of the exit, the payload
value and the position of the exit among the ordered exits. Two exits of
the same type with the same payload are told apart. -/
theorem ExitAt.value_inj {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B)
    (x : LetSeq.StraightLine.Structural.Value (α := α) A) (y : LetSeq.StraightLine.Structural.Value (α := α) B)
    (same : e.value x = e'.value y) : ∃ type : A = B, type ▸ x = y ∧ e.index = e'.index :=
  exit_value_index_proof e e' x y same

omit [TaggedSignature α Φ] in
/-- An assembled payload is determined by its value at an environment that
separates the atom slots. The payload grammar has one tree for each
product of atom slots, so a changed component or a changed order is a
different value. -/
theorem payload_value_injective {A : Ty α} {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β}
    {used : Set Nat} (sep : Separates ρ used) : Function.Injective (Assembly.value (A := A) ρ) :=
  payload_inj_proof sep

/-- A leaf returns the value of its payload at its exit. -/
theorem run_ret {A : Ty α} (exit : ExitAt L A) (payload : Assembly β A)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ret (Φ := Φ) exit payload).typing ρ = pure (exit.value (payload.value ρ)) :=
  run_ret_proof exit payload ρ

/-- The leaf reflection. Two leaves with the same ordered traces at an
environment that separates the atom slots return at the same exit
position, at the same exit type, the same payload tree. -/
theorem ret_eq_of_run {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B) (p : Assembly β A) (q : Assembly β B)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) {used : Set Nat} (sep : Separates ρ used)
    (same : run (CaseTree.ret (Φ := Φ) e p).typing ρ = run (CaseTree.ret (Φ := Φ) e' q).typing ρ) :
    ∃ type : A = B, type ▸ p = q ∧ e.index = e'.index :=
  ret_eq_of_run_proof e e' p q ρ sep same

/-! ## Separation of case trees -/

/-- The token induction, at any pending state. Two case trees whose runs
agree at the environments of `TokenWitness` are the same term. -/
theorem caseTree_eq_of_witness {pending : Pending α} (p : CaseTree pending β L t) (q : CaseTree pending β L u)
    (k : Nat) (witness : TokenWitness pending β k (fun ρ => run p.typing ρ = run q.typing ρ)) : t = u :=
  caseTree_eq_of_witness_proof p q k witness

/-- Two case trees with the same ordered traces at one environment that
separates the atom slots are the same term. -/
theorem caseTree_eq_of_run (p : CaseTree .body β L t) (q : CaseTree .body β L u)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) (k : Nat)
    (sep : Separates ρ (Set.Iio k)) (same : run p.typing ρ = run q.typing ρ) : t = u :=
  caseTree_eq_of_run_proof p q ρ k sep same

/-- The ordered trace interpretation with atoms reflects native equality
of branching operands over a separable bound context. -/
theorem branching_reflects (separable : Separable β) (x y : Operand Φ β (packedExitType L))
    (hx : Branching x) (hy : Branching y) (same : traceArrow x.2 = traceArrow y.2) :
    Equiv false Γ₀ β x.1 y.1 (packedExitType L) :=
  branching_reflects_proof x y hx hy separable same

/-- Over a separable bound context, two case trees are natively equal
exactly when they are the same term. -/
theorem caseTree_equiv_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    Equiv false Γ₀ β t u (packedExitType L) ↔ t = u :=
  ⟨fun h => by
      obtain ⟨ρ, k, sep⟩ := separable
      exact caseTree_eq_of_run p q ρ k sep ((LetCase.Structural.Reply.traceArrow_eq_iff_run p.typing q.typing).mp
        (LetCase.Structural.Reply.traceArrow_of_valid
          (LetCase.Structural.Reply.valid_of_equiv p.typing q.typing h)) ρ),
    fun same => by
      cases same
      exact .refl p.typing.toHasType⟩

/-! ## Branching operands -/

/-- A case tree is a branching operand. -/
theorem branching_operand (p : CaseTree .body β L t) : Branching p.operand :=
  ⟨t, p, .refl p.typing.toHasType⟩

/-- An operand natively equal to a branching operand is branching. -/
theorem Branching.congr {x y : Operand Φ β (packedExitType L)}
    (h : Equiv false Γ₀ β x.1 y.1 (packedExitType L)) (branching : Branching y) : Branching x :=
  let ⟨t, p, same⟩ := branching
  ⟨t, p, h.trans same⟩

/-- The graph read back from a case tree emits a branching operand. -/
theorem branching_graph (p : CaseTree .body β L t) : Branching p.graph.toLetCase :=
  ⟨t, p, CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing⟩

/-- Entries with branching emitted operands are reflected by the ordered
trace interpretation with atoms. -/
theorem branching_traceReflects (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    TraceReflects l r :=
  branching_reflects separable _ _ hl hr

/-! ## Soundness and completeness -/

/-- A ranked sentence between entries with branching emitted operands,
over a separable bound context, holds in every supported model of the
ranked room exactly when the emitted operands are natively equal. -/
theorem rankedValid_branching_iff (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1
        (packedExitType L) :=
  (rankedValid_iff_of_traceReflects (sentenceOf l r) (branching_traceReflects separable l r hl hr)).trans
    (derivable_iff false (sentenceOf l r))

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_branching_iff_atomTrace (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_iff_atomTrace (sentenceOf l r) (branching_traceReflects separable l r hl hr)

/-- On the graphs read back from two case trees, validity in the ranked
room is equality of the two trees. The sentence is at the original ordered
exits. -/
theorem rankedValid_caseTree_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    RankedValid false (sentenceOf (entryOf p.graph) (entryOf q.graph)) ↔ t = u :=
  (rankedValid_branching_iff separable (entryOf p.graph) (entryOf q.graph) (branching_graph p)
    (branching_graph q)).trans
    (Iff.trans
      ⟨fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).symm.trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing),
        fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing).symm⟩
      (caseTree_equiv_iff separable p q))

/-- At the ordered trace model with atoms, the original ordered-exit
arrows of the graphs read back from two case trees are equal exactly when
the trees are the same. The arrows are those of the ranked room, into the
ordered exits, before any packing. -/
theorem denoteRanked_caseTree_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf p.graph) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔ t = u :=
  (rankedValid_branching_iff_atomTrace separable (entryOf p.graph) (entryOf q.graph) (branching_graph p)
    (branching_graph q)).symm.trans (rankedValid_caseTree_iff separable p q)

/-! ## The renaming action on case trees

A body is renamed along any renaming of its context. A pending tuple or
reply is renamed along a renaming of the context beneath its pending slot,
which stays newest. The action is defined by one recursion over all three
kinds of tree. -/

section Renaming

variable {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}

omit [TaggedSignature α Φ] in
/-- Renaming commutes with returning at an exit. -/
theorem ExitAt.term_rename {A : Ty α} (e : ExitAt L A) (ξ : Fin n → Fin m)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) : (e.term t).rename ξ = e.term (t.rename ξ) :=
  exit_term_rename_proof e ξ t

omit [TaggedSignature α Φ] in
/-- Renaming commutes with assembling a payload or an argument. -/
theorem argTerm_rename {A : Ty α} (p : Assembly β A) (ρ : BoundCtx.Renaming β γ) :
    (argTerm (Φ := Φ) p).rename ρ.toFun = argTerm (p.rename ρ) :=
  argTerm_rename_proof p ρ

omit [TaggedSignature α Φ] in
/-- Two renamings with the same function are equal. -/
theorem renaming_ext {ρ π : BoundCtx.Renaming β γ} (same : ∀ i, ρ.toFun i = π.toFun i) : ρ = π :=
  renaming_ext_proof same

omit [TaggedSignature α Φ] in
/-- Lifting under a new slot commutes with composition. -/
theorem renaming_up_comp (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) (X : Ty α) :
    (ρ.up X).comp (π.up X) = (ρ.comp π).up X :=
  renaming_up_comp_proof ρ π X

omit [TaggedSignature α Φ] in
/-- Renaming an assembled payload twice is renaming along the composite. -/
theorem assembly_rename_comp {A : Ty α} (p : Assembly β A) (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) : (p.rename ρ).rename π = p.rename (ρ.comp π) :=
  assembly_rename_comp_proof p ρ π

end Renaming

/-- The term of a renamed case tree is the renamed term. For a body:
`(tree.renamed ρ).1 = t.rename ρ`. Under a pending slot the renaming keeps
that slot: `(tree.renamed ρ).1 = t.rename (up ρ)`. -/
theorem CaseTree.renamed_term {pending : Pending α} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (tree : CaseTree pending β L t) {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : CaseTree.Along pending β γ) :
    CaseTree.RenamedTerm pending β γ t ρ (tree.renamed ρ) :=
  renamed_term_proof tree ρ

/-- Renaming a case tree twice is renaming it along the composite:
`(tree.renamed ρ).2.renamed π = tree.renamed (ρ.comp π)`, for a body and
for a pending tree. -/
theorem CaseTree.renamed_comp {pending : Pending α} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (tree : CaseTree pending β L t) : CaseTree.RenamedComp pending β tree :=
  renamed_comp_proof tree

/-- The renamed body, with its term stated. -/
theorem CaseTree.renamed_body_term {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t)
    {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    (CaseTree.renamed (pending := .body) tree ρ).1 = t.rename ρ.toFun :=
  CaseTree.renamed_term tree ρ

/-- Renaming a body twice is renaming it along the composite. -/
theorem CaseTree.renamed_body_comp {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t)
    {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .body) (CaseTree.renamed (pending := .body) tree ρ).2 π =
      CaseTree.renamed (pending := .body) tree (ρ.comp π) :=
  CaseTree.renamed_comp tree ρ π

/-! ## Telescopes

The renaming that moves a slot bound after a telescope beneath it commutes
with renaming the context. The move of two slots is composed from it. -/

section Tele

variable {k j i : Nat} {Ω : BoundCtx (Ty α) k} {Ω' : BoundCtx (Ty α) j} {Ω'' : BoundCtx (Ty α) i}

omit [TaggedSignature α Φ] in
/-- Lifting under a telescope commutes with composition. -/
theorem upTele_comp (tel : List (Ty α)) (ρ : BoundCtx.Renaming Ω Ω') (π : BoundCtx.Renaming Ω' Ω'') :
    (upTele ρ tel).comp (upTele π tel) = upTele (ρ.comp π) tel :=
  upTele_comp_proof tel ρ π

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope commutes with renaming. -/
theorem weakenTele_natural (tel : List (Ty α)) (ρ : BoundCtx.Renaming Ω Ω') :
    (weakenTele Ω tel).comp (upTele ρ tel) = ρ.comp (weakenTele Ω' tel) :=
  weakenTele_natural_proof tel ρ

omit [TaggedSignature α Φ] in
/-- Moving a slot beneath a telescope commutes with renaming. -/
theorem swapTele_natural (tel : List (Ty α)) (ω : BoundCtx.Renaming Ω Ω') (T : Ty α) :
    (swapTele Ω tel T).comp (upTele (ω.up T) tel) = ((upTele ω tel).up T).comp (swapTele Ω' tel T) :=
  swapTele_natural_proof tel ω T

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope under a new slot, and then moving the slot
beneath the telescope, is weakening past the telescope over the slot. -/
theorem swapTele_weaken (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) (T : Ty α) :
    ((weakenTele Ω tel).up T).comp (swapTele Ω tel T) = weakenTele (Ω.snoc T) tel :=
  swapTele_weaken_proof tel Ω T

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath a telescope commutes with renaming. -/
theorem pairPastTele_natural (tel : List (Ty α)) (ω : BoundCtx.Renaming Ω Ω') (A B : Ty α) :
    (pairPastTele Ω tel A B).comp (upTele ((ω.up A).up B) tel) =
      (((upTele ω tel).up A).up B).comp (pairPastTele Ω' tel A B) :=
  pairPastTele_natural_proof tel ω A B

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath a telescope with one more oldest slot: move
them beneath the rest, then beneath that slot. -/
theorem pairPastTele_cons (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) (X A B : Ty α) :
    pairPastTele Ω (X :: tel) A B =
      (pairPastTele (Ω.snoc X) tel A B).comp (upTele (afterPairRenaming Ω X A B) tel) :=
  pairPastTele_cons_proof tel Ω X A B

omit [TaggedSignature α Φ] in
/-- Exchanging two slots commutes with renaming beneath them. -/
theorem swapRenaming_natural (ω : BoundCtx.Renaming Ω Ω') (X T : Ty α) :
    (swapRenaming Ω X T).comp ((ω.up T).up X) = ((ω.up X).up T).comp (swapRenaming Ω' X T) :=
  swapRenaming_natural_proof ω X T

omit [TaggedSignature α Φ] in
/-- Lifting the identity under a telescope is the identity. -/
theorem upTele_id (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) :
    upTele (BoundCtx.Renaming.id Ω) tel = .id _ :=
  upTele_id_proof tel Ω

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath one slot is the move of three slots. -/
theorem pairPastTele_single (Ω : BoundCtx (Ty α) k) (X A B : Ty α) :
    pairPastTele Ω [X] A B = afterPairRenaming Ω X A B :=
  pairPastTele_single_proof Ω X A B

omit [TaggedSignature α Φ] in
/-- The newest of two slots moved beneath a telescope lands where
weakening past the telescope puts it. -/
theorem pairPastTele_zero (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) (A B : Ty α) :
    (pairPastTele Ω tel A B).toFun 0 = (weakenTele ((Ω.snoc A).snoc B) tel).toFun 0 :=
  pairPastTele_zero_proof tel Ω A B

omit [TaggedSignature α Φ] in
/-- Moving a telescope beneath a telescope commutes with renaming. -/
theorem swapTeles_natural (H tel : List (Ty α)) (ω : BoundCtx.Renaming Ω Ω') :
    (swapTeles Ω tel H).comp (upTele (upTele ω H) tel) = (upTele (upTele ω tel) H).comp (swapTeles Ω' tel H) :=
  swapTeles_natural_proof H tel ω

omit [TaggedSignature α Φ] in
/-- Moving a telescope that starts with two slots: move the two slots,
then the rest. -/
theorem swapTeles_pair (H : List (Ty α)) (Ω : BoundCtx (Ty α) k) (tel : List (Ty α)) (A B : Ty α) :
    swapTeles Ω tel (A :: B :: H) =
      (upTele (pairPastTele Ω tel A B) H).comp (swapTeles ((Ω.snoc A).snoc B) tel H) :=
  swapTeles_pair_proof H Ω tel A B

omit [TaggedSignature α Φ] in
/-- Moving a telescope beneath a telescope with one more oldest slot: move
it beneath the rest, then beneath that slot. -/
theorem swapTeles_cons (H : List (Ty α)) (Ω : BoundCtx (Ty α) k) (X : Ty α) (tel : List (Ty α)) :
    swapTeles Ω (X :: tel) H = (swapTeles (Ω.snoc X) tel H).comp (upTele (swapTeles Ω [X] H) tel) :=
  swapTeles_cons_proof H Ω X tel

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope over a slot, and then moving the telescope
beneath the slot, is weakening past the telescope under the slot. -/
theorem swapTeles_weaken (H : List (Ty α)) (Ω : BoundCtx (Ty α) k) (T : Ty α) :
    (weakenTele (Ω.snoc T) H).comp (swapTeles Ω [T] H) = (weakenTele Ω H).up T :=
  swapTeles_weaken_proof H Ω T

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope, under two new slots, and then moving the
two slots beneath the telescope, is weakening past the telescope over the
two slots. -/
theorem pairPastTele_weaken (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) (A B : Ty α) :
    (((weakenTele Ω tel).up A).up B).comp (pairPastTele Ω tel A B) = weakenTele ((Ω.snoc A).snoc B) tel :=
  pairPastTele_weaken_proof tel Ω A B

omit [TaggedSignature α Φ] in
/-- Weakening past two telescopes and then exchanging them is weakening
past them in the other order. -/
theorem swapTeles_weakenTele (H : List (Ty α)) (Ω : BoundCtx (Ty α) k) (tel : List (Ty α)) :
    ((weakenTele Ω tel).comp (weakenTele (extendCtx Ω tel) H)).comp (swapTeles Ω tel H) =
      (weakenTele Ω H).comp (weakenTele (extendCtx Ω H) tel) :=
  swapTeles_weakenTele_proof H Ω tel

omit [TaggedSignature α Φ] in
/-- Two pairs of slots move past each other in two steps. -/
theorem afterPairPair_split (Γ : BoundCtx (Ty α) k) (C D A B : Ty α) :
    afterPairPairRenaming Γ C D A B =
      (afterPairRenaming (Γ.snoc C) D A B).comp ((afterPairRenaming Γ C A B).up D) :=
  afterPairPair_split_proof Γ C D A B

omit [TaggedSignature α Φ] in
/-- Renaming commutes with the pattern lets that unpack a tuple slot. -/
theorem unpackAt_rename (atoms : List α) (ρ : BoundCtx.Renaming Ω Ω') (s : Fin k)
    (u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))) :
    (unpackAt atoms s u).rename ρ.toFun =
      unpackAt atoms (ρ.toFun s) (u.rename (upTele ρ (pairsTele atoms)).toFun) :=
  unpackAt_rename_proof atoms ρ s u

/-- Renaming the pending tuple whose unpacking ends in a body is the
pending tuple whose unpacking ends in the renamed body. -/
theorem CaseTree.packed_renamed (atoms : List α)
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))}
    (r : CaseTree .body (extendCtx Ω (unpackTele atoms)) L u) (ω : BoundCtx.Renaming Ω Ω') :
    CaseTree.renamed (pending := .tuple atoms) (β := Ω.snoc (tupleTy atoms)) (CaseTree.packed atoms r) ω =
      ⟨_, CaseTree.packed atoms (CaseTree.renamed (pending := .body) r (upTele ω (unpackTele atoms))).2⟩ :=
  packed_renamed_proof atoms r ω

omit [TaggedSignature α Φ] in
/-- Moving a telescope beneath the empty telescope is the identity. -/
theorem swapTeles_nil (H : List (Ty α)) (Ω : BoundCtx (Ty α) k) : swapTeles Ω [] H = .id _ :=
  swapTeles_nil_proof H Ω

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope over another telescope, and then exchanging
the two, is weakening past the first under the second. -/
theorem swapTeles_weaken_up (tel : List (Ty α)) (Ω : BoundCtx (Ty α) k) (H : List (Ty α)) :
    (weakenTele (extendCtx Ω tel) H).comp (swapTeles Ω tel H) = upTele (weakenTele Ω H) tel :=
  swapTeles_weaken_up_proof tel Ω H

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath two slots is the exchange of two pairs. -/
theorem pairPastTele_pair (Ω : BoundCtx (Ty α) k) (C D A B : Ty α) :
    pairPastTele Ω [C, D] A B = afterPairPairRenaming Ω C D A B :=
  pairPastTele_pair_proof Ω C D A B

end Tele

/-! ## Stacks of packed tuples

The renamings of a context under the unpackings of a stack satisfy the
laws of the telescope renamings they are built from. The stack has any
depth. -/

section Stack

variable {k j i : Nat} {Ω : BoundCtx (Ty α) k} {Ω' : BoundCtx (Ty α) j}

omit [TaggedSignature α Φ] in
/-- Renaming the slots of a stack twice is renaming along the composite. -/
theorem Holds.rename_comp {Ω'' : BoundCtx (Ty α) i} {stack : List (List α)} (H : Holds Ω stack)
    (ρ : BoundCtx.Renaming Ω Ω') (π : BoundCtx.Renaming Ω' Ω'') :
    (H.rename ρ).rename π = H.rename (ρ.comp π) :=
  holds_rename_comp_proof ρ π H

omit [TaggedSignature α Φ] in
/-- Weakening past the unpackings of a stack commutes with renaming. -/
theorem weakenStack_natural (stack : List (List α)) (π : BoundCtx.Renaming Ω Ω') :
    (weakenStack stack Ω).comp (upStack stack π) = π.comp (weakenStack stack Ω') :=
  weakenStack_natural_proof stack π

omit [TaggedSignature α Φ] in
/-- Moving a telescope beneath the unpackings of a stack commutes with
renaming. -/
theorem swapStack_natural (stack : List (List α)) (tel : List (Ty α)) (π : BoundCtx.Renaming Ω Ω') :
    (swapStack stack Ω tel).comp (upTele (upStack stack π) tel) =
      (upStack stack (upTele π tel)).comp (swapStack stack Ω' tel) :=
  swapStack_natural_proof stack tel π

omit [TaggedSignature α Φ] in
/-- Weakening past the unpackings of a stack over a telescope, and then
moving the telescope beneath them, is weakening past them under the
telescope. -/
theorem swapStack_weaken (stack : List (List α)) (Ω : BoundCtx (Ty α) k) (tel : List (Ty α)) :
    (weakenStack stack (extendCtx Ω tel)).comp (swapStack stack Ω tel) = upTele (weakenStack stack Ω) tel :=
  swapStack_weaken_proof stack Ω tel

omit [TaggedSignature α Φ] in
/-- Weakening past a telescope and then past the unpackings of a stack,
and then moving the telescope beneath them, is weakening in the other
order. -/
theorem swapStack_weakenTele (stack : List (List α)) (Ω : BoundCtx (Ty α) k) (tel : List (Ty α)) :
    ((weakenTele Ω tel).comp (weakenStack stack (extendCtx Ω tel))).comp (swapStack stack Ω tel) =
      (weakenStack stack Ω).comp (weakenTele (stackCtx stack Ω) tel) :=
  swapStack_weakenTele_proof stack Ω tel

omit [TaggedSignature α Φ] in
/-- Moving a telescope with one more oldest slot beneath the unpackings of
a stack: move the rest, then that slot. -/
theorem swapStack_cons (stack : List (List α)) (Ω : BoundCtx (Ty α) k) (X : Ty α) (tel : List (Ty α)) :
    swapStack stack Ω (X :: tel) =
      (swapStack stack (Ω.snoc X) tel).comp (upTele (swapStack stack Ω [X]) tel) :=
  swapStack_cons_proof stack Ω X tel

omit [TaggedSignature α Φ] in
/-- Selecting a tuple commutes with renaming the slots of the stack. -/
theorem Holds.select_rename {stack : List (List α)} {atoms : List α} {rest : List (List α)}
    (sel : Select stack atoms rest) (H : Holds Ω stack) (ρ : BoundCtx.Renaming Ω Ω') :
    (H.rename ρ).select sel = (H.select sel).rename ρ :=
  holds_select_rename_proof ρ sel H

omit [TaggedSignature α Φ] in
/-- Weakening past the unpackings of a stack with a tuple selected, and
then moving the selected unpacking to its place, is weakening past the
unpackings of the stack. -/
theorem selectRen_weaken {stack : List (List α)} {atoms : List α} {rest : List (List α)}
    (sel : Select stack atoms rest) (Ω : BoundCtx (Ty α) k) :
    (weakenStack (atoms :: rest) Ω).comp (selectRen sel Ω) = weakenStack stack Ω :=
  selectRen_weaken_proof sel Ω

omit [TaggedSignature α Φ] in
/-- Moving a selected unpacking to its place commutes with renaming. -/
theorem selectRen_natural {stack : List (List α)} {atoms : List α} {rest : List (List α)}
    (sel : Select stack atoms rest) (π : BoundCtx.Renaming Ω Ω') :
    (selectRen sel Ω).comp (upStack stack π) = (upStack (atoms :: rest) π).comp (selectRen sel Ω') :=
  selectRen_natural_proof sel π

end Stack

/-! ## Renaming and binding under a pending tuple

Binding a telescope under the unpacking of a pending tuple commutes with
renaming the tuple beforehand and with renaming the result. -/

/-- Binding a telescope under a renamed pending tuple is binding it under
the tuple along the composite renaming. -/
theorem CaseTree.pushed_renamed {atoms : List α} {T : Ty α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (tree : CaseTree (.tuple atoms) (β.snoc T) L t) {j : Nat} {β' : BoundCtx (Ty α) j}
    (ρ : BoundCtx.Renaming β β') {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (π : BoundCtx.Renaming β' (extendCtx Ω tel)) (wrap : CaseTree.Wrap Φ L Ω tel) :
    CaseTree.pushed (pending := .tuple atoms) (β := β'.snoc T)
      (CaseTree.renamed (pending := .tuple atoms) tree ρ).2 π wrap = CaseTree.pushed tree (ρ.comp π) wrap :=
  pushed_pre_proof tree ρ π wrap

/-- Renaming the result of binding a telescope under a pending tuple is
binding the telescope under the tuple along the composite renaming, with
the binding taken after the renaming. The way to bind the telescope must
commute with renaming. -/
theorem CaseTree.renamed_pushed {atoms : List α} {T : Ty α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (tree : CaseTree (.tuple atoms) (β.snoc T) L t) {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (π : BoundCtx.Renaming β (extendCtx Ω tel)) (wrap : CaseTree.Wrap Φ L Ω tel) (natural : wrap.Natural)
    {j : Nat} {Ω' : BoundCtx (Ty α) j} (ω : BoundCtx.Renaming Ω Ω') :
    CaseTree.renamed (pending := .tuple atoms) (β := Ω.snoc T) (CaseTree.pushed tree π wrap).2 ω =
      CaseTree.pushed tree (π.comp (upTele ω tel)) (fun ω' => wrap (ω.comp ω')) :=
  pushed_post_proof tree π wrap natural ω

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
