module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic
import Silmaril.Proofs.Games.Abstract.FullFun.Laws
import Silmaril.Proofs.Games.Abstract.FullFun.Tensor
import Silmaril.Proofs.Games.Abstract.FullFun.Unfold
import Silmaril.Proofs.Games.Abstract.FullFun.Natural
import Silmaril.Proofs.Games.Abstract.FullFun.Dinat
import Silmaril.Proofs.Games.Abstract.FullFun.Codiag
import Silmaril.Proofs.Games.Abstract.FullFun.Uniform
import Silmaril.Games.Abstract.Function.Thms
import Silmaril.Games.Abstract.FunctionIter.Thms

/-!
# Full observations of functions: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.FullFun`.

* `consistent_append`: consistency of a joined stream `c ++ₛ ω` splits exactly into the
  finished prefix `c` and the tail `ω`;
* `hostObsInf_seq` (**host preservation of sequencing**): the productive observations of
  `FullFun.seq f g` against a relational host are those of `f`, or a finished return of `f`
  with a consistent log followed by a productive observation of `g`;
* `pure_inf`, `pure_seq_inf`: the identity has no productive run, and does not change the
  productive runs of what follows;
* `FullFun.seq_assoc_fin`, `FullFun.seq_assoc_inf`, `FullFun.seq_assoc`: sequencing is
  associative, finite part (`AFun.seq`) and productive runs;
* `FullFun.seq_pure_inf`, `FullFun.seq_pure`, `FullFun.pure_seq`: the identity is a unit on
  both sides;
* `FullFun.iter_fin`: the finite part of iteration is `AFun.iter`;
* `streamPrefix_appendStream`, `appendStream_chain`, `streamConcat_of_appendChain`: stream
  bookkeeping for `++ₛ`, as `Shape.streamAppend_chain` for `++ω`;
* `consistent_streamConcat`: consistency of a concatenated stream (`Shape.StreamConcat`) is
  consistency of every segment;
* `hostObsInf_iter` (**host preservation of iteration**): the productive observations of
  `FullFun.iter F` against a relational host are (a) a consistent finite continuing chain
  followed by a productive observation of the next iteration, or (b) an infinite continuing
  chain with every segment consistent.

**Copairing and the fixpoint law** (`Silmaril.Proofs.Games.Abstract.FullFun.Unfold`):

* `FullFun.pure_fin`, `FullFun.case_fin`: the finite parts are `AFun.pure` and `AFun.case`;
* `FullFun.comap_inl_case`, `FullFun.comap_inr_case`, `FullFun.pure_map_inl_seq_case`,
  `FullFun.pure_map_inr_seq_case`: copairing after an injection is the corresponding component;
* `FullFun.case_pure_map`: the copairing of the injections is the identity;
* `FullFun.seq_case`: sequencing distributes over copairing on the left;
* `FullFun.iter_unfold` (**the fixpoint law**): `iter F = seq F (case pure (iter F))`, with no
  hypothesis on `F`. The finite part is `AFun.iter_unfold`. For the productive runs, a finite
  continuing chain followed by a productive run is empty or a first continuing iteration
  followed by a shorter chain, and an infinite continuing chain is its first iteration followed
  by the shifted chain (`streamConcat_tail`, `streamConcat_cons`).

**Pure maps and whiskering** (`Silmaril.Proofs.Games.Abstract.FullFun.Tensor`):

* `FullFun.mem_map`: the finite behaviours of `f.map h` are those of `f` with `h` applied to
  returned values;
* `FullFun.map_id`, `FullFun.map_map`, `FullFun.comap_id`, `FullFun.comap_comap`,
  `FullFun.map_comap`: functoriality of post- and pre-composition;
* `FullFun.seq_pure_map`, `FullFun.pure_map_seq`, `FullFun.seq_map`, `FullFun.map_seq`,
  `FullFun.comap_seq`: interaction with sequencing;
* `FullFun.whiskerRight_pure`, `FullFun.whiskerRight_seq`, `FullFun.whiskerLeft_pure`,
  `FullFun.whiskerLeft_seq`: whiskering is functorial (`(- ⋉ C)` and `(C ⋊ -)` preserve the
  identity and sequencing);
* `FullFun.interchange_pure_left`, `FullFun.interchange_pure_right`: the interchange law holds
  when one of the two functions is a pure map;
* `FullFun.not_interchange`: it fails for two effectful functions (two single calls are logged
  in the order they run), so full observations form a premonoidal and not a monoidal
  structure;
* `hostObsInf_map`, `hostObsInf_comap`, `hostObsInf_whiskerRight`, `hostObsInf_whiskerLeft`:
  host preservation; the productive observations are those of the original function.

**Naturality and uniformity of iteration** (`Silmaril.Proofs.Games.Abstract.FullFun.Natural`).
No hypothesis on the loop bodies beyond the stated equation. Divergence (`div` ends and
infinite silent chains) and productive runs are included:

* `FullFun.iter_map_fin`, `FullFun.iter_map` (**naturality in the output**):
  `iter (F.map (Sum.map h id)) = (iter F).map h`. Mapping the exit value changes no continuing
  iteration (`FullFun.contChain_map`);
* `FullFun.iter_uniform_fin`, `FullFun.iter_uniform_comap`, `FullFun.iter_uniform`
  (**uniformity** for a pure map `h : A' → A`): if `h ; F = G ; [inl, inr ∘ h]`, that is
  `F.comap h = G.map (Sum.map id h)`, then `h ; iter F = iter G`. A run of `G` maps to a run of
  `F` (`FullFun.contChain_uniform`). A run of `F` from `h a` lifts, iteration by iteration, to
  a run of `G` from `a` (`FullFun.contChain_lift`), infinite chains by dependent choice.
  Uniformity is claimed only for pure `h`, as for Elgot uniformity;
* `FullFun.case_pure_map_map`: the copairing of pure maps is a pure map.

**Dinaturality of iteration** (`Silmaril.Proofs.Games.Abstract.FullFun.Dinat`), with no
hypothesis on the bodies:

* `FullFun.iter_dinat`: for `f : A → B ⊕ C` and `g : C → B ⊕ A`,
  `iter (f ; [inl, g]) = f ; [id, iter (g ; [inl, f])]`. Both sides run `f, g, f, g, …` until
  an `inl` exit; traps and `div` ends of either function, infinite silent chains and productive
  runs correspond. An infinite chain's logs `cf 0 ++ cg 0, cf 1 ++ cg 1, …` are regrouped as
  `cf 0` followed by `cg 0 ++ cf 1, cg 1 ++ cf 2, …`.

**The codiagonal law** (`Silmaril.Proofs.Games.Abstract.FullFun.Codiag`), with no hypothesis:

* `FullFun.iter_codiag`: for `F : A → (B ⊕ A) ⊕ A`,
  `iter (iter F) = iter (F.map [id, inr])` (`F.map h = F ; pure.map h`, `FullFun.seq_pure_map`).
  The inner loop continues on `inr` and its `inl (inr a')` exit continues the outer loop; merging
  the tags gives one loop. A merged chain with infinitely many outer steps is an infinite chain
  of outer iterations; with finitely many, a finite chain of outer iterations followed by an
  infinite inner chain (silent: inner divergence; productive: an inner productive run). An
  infinite chain of outer iterations, each a finite merged chain, is laid end to end into one
  merged chain; silent iterations give a silent chain.

**Uniformity fails along effectful maps** (`Silmaril.Proofs.Games.Abstract.FullFun.Uniform`).
With `G = pure.map inr` (continue silently forever, so `iter G` is `([], div)`), `F = G`, and
`h ; F = G ; [inl, inr ∘ h]`:

* `FullFun.not_iter_uniform_call`: `h` makes one import call and returns (total and
  deterministic). Then `h ; iter F` makes the call before diverging, `([x], div)`, while
  `iter G` diverges silently. The logs differ, so this survives merging trap and divergence;
* `FullFun.not_iter_uniform_trap`: `h` always traps (strict: it preserves divergence). Then
  `h ; iter F` traps while `iter G` diverges.

So uniformity is claimed only along pure maps; total, deterministic or strict maps are not
enough.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- Consistency of a joined stream splits into the prefix and the tail. -/
theorem consistent_append {R : HostRel E} (c : List (Call E)) (ω : Nat → Call E) :
    (∀ n, R ((c ++ₛ ω) n).1 (.answer ((c ++ₛ ω) n).2)) ↔
      R.Consistent c ∧ ∀ n, R (ω n).1 (.answer (ω n).2) :=
  Silmaril.Proofs.Games.Abstract.FullFun.consistent_append c ω

/-- **Host preservation of sequencing** (productive part). -/
theorem hostObsInf_seq {R : HostRel E} (f : FullFun E S A B) (g : FullFun E S B C) (s : S)
    (a : A) (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.seq f g).2 s a ↔
      ω ∈ hostObsInf R f.2 s a ∨
        ∃ (c : List (Call E)) (b : B) (s₁ : S) (ω' : Nat → Call E),
          (c, End.ret b s₁) ∈ f.1 s a ∧ R.Consistent c ∧ ω' ∈ hostObsInf R g.2 s₁ b ∧
          ω = c ++ₛ ω' :=
  Silmaril.Proofs.Games.Abstract.FullFun.hostObsInf_seq f g s a ω

/-- The identity has no productive run. -/
theorem FullFun.pure_inf (s : S) (a : A) : (FullFun.pure : FullFun E S A A).2 s a = ∅ := rfl

/-- Sequencing after the identity keeps the productive runs. -/
theorem FullFun.pure_seq_inf (g : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq FullFun.pure g).2 s a = g.2 s a :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_seq_inf g s a

/-- **Associativity of sequencing**, finite part. -/
theorem FullFun.seq_assoc_fin {D : Type u} (f : AFun E S A B) (g : AFun E S B C)
    (h : AFun E S C D) : AFun.seq (AFun.seq f g) h = AFun.seq f (AFun.seq g h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_assoc_fin f g h

/-- **Associativity of sequencing**, productive runs. -/
theorem FullFun.seq_assoc_inf {D : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (h : FullFun E S C D) :
    (FullFun.seq (FullFun.seq f g) h).2 = (FullFun.seq f (FullFun.seq g h)).2 :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_assoc_inf f g h

/-- **Associativity of sequencing.** -/
theorem FullFun.seq_assoc {D : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (h : FullFun E S C D) : FullFun.seq (FullFun.seq f g) h = FullFun.seq f (FullFun.seq g h) :=
  Prod.ext (FullFun.seq_assoc_fin f.1 g.1 h.1) (FullFun.seq_assoc_inf f g h)

/-- The identity is a right unit. -/
theorem FullFun.seq_pure (f : FullFun E S A B) : FullFun.seq f FullFun.pure = f :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_pure f

/-- Sequencing before the identity keeps the productive runs. -/
theorem FullFun.seq_pure_inf (f : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq f FullFun.pure).2 s a = f.2 s a := by
  rw [FullFun.seq_pure]

/-- The identity is a left unit. -/
theorem FullFun.pure_seq (g : FullFun E S A B) : FullFun.seq FullFun.pure g = g :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_seq g

/-- The finite part of iteration is `AFun.iter`. -/
theorem FullFun.iter_fin (F : FullFun E S A (B ⊕ A)) : (FullFun.iter F).1 = AFun.iter F.1 := rfl

/-- A list is a prefix of itself in front of a stream. -/
theorem streamPrefix_appendStream {α : Type u} (c : List α) (ω : Nat → α) :
    Shape.StreamPrefix c (c ++ₛ ω) :=
  Silmaril.Proofs.Games.Abstract.FullFun.streamPrefix_appendStream c ω

/-- A chain of streams, each a segment in front of the next. -/
theorem appendStream_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1)) (n : Nat) :
    w 0 = ((List.range n).flatMap cs) ++ₛ w n :=
  Silmaril.Proofs.Games.Abstract.FullFun.appendStream_chain h n

/-- A chain of streams of unbounded total length is the concatenation of its segments. -/
theorem streamConcat_of_appendChain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1))
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap cs).length) : Shape.StreamConcat cs (w 0) :=
  Silmaril.Proofs.Games.Abstract.FullFun.streamConcat_of_appendChain h hu

/-- Consistency of a concatenated stream is consistency of every segment. -/
theorem consistent_streamConcat {R : HostRel E} {l : Nat → List (Call E)} {ω : Nat → Call E}
    (h : Shape.StreamConcat l ω) :
    (∀ n, R (ω n).1 (.answer (ω n).2)) ↔ ∀ n, R.Consistent (l n) :=
  Silmaril.Proofs.Games.Abstract.FullFun.consistent_streamConcat h

/-- **Host preservation of iteration** (productive part). -/
theorem hostObsInf_iter {R : HostRel E} (F : FullFun E S A (B ⊕ A)) (s : S) (a : A)
    (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.iter F).2 s a ↔
      (∃ (c : List (Call E)) (s' : S) (a' : A) (ω' : Nat → Call E),
          FullFun.ContChain F.1 s a c s' a' ∧ R.Consistent c ∧ ω' ∈ hostObsInf R F.2 s' a' ∧
          ω = c ++ₛ ω') ∨
        ∃ (σ : Nat → S × A) (l : Nat → List (Call E)), σ 0 = (s, a) ∧
          (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ F.1 (σ n).1 (σ n).2) ∧
          (∀ n, R.Consistent (l n)) ∧ Shape.StreamConcat l ω :=
  Silmaril.Proofs.Games.Abstract.FullFun.hostObsInf_iter F s a ω

/-! ## Copairing and the fixpoint law -/

theorem FullFun.pure_fin : (FullFun.pure : FullFun E S A A).1 = AFun.pure := rfl

theorem FullFun.case_fin (g : FullFun E S A C) (h : FullFun E S B C) :
    (FullFun.case g h).1 = AFun.case g.1 h.1 := rfl

theorem FullFun.comap_inl_case (g : FullFun E S A C) (h : FullFun E S B C) :
    (FullFun.case g h).comap Sum.inl = g := rfl

theorem FullFun.comap_inr_case (g : FullFun E S A C) (h : FullFun E S B C) :
    (FullFun.case g h).comap Sum.inr = h := rfl

/-- Copairing after the left injection is the left component. -/
theorem FullFun.pure_map_inl_seq_case (g : FullFun E S A C) (h : FullFun E S B C) :
    FullFun.seq (FullFun.pure.map Sum.inl) (FullFun.case g h) = g :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_map_seq Sum.inl _

/-- Copairing after the right injection is the right component. -/
theorem FullFun.pure_map_inr_seq_case (g : FullFun E S A C) (h : FullFun E S B C) :
    FullFun.seq (FullFun.pure.map Sum.inr) (FullFun.case g h) = h :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_map_seq Sum.inr _

/-- The copairing of the injections is the identity. -/
theorem FullFun.case_pure_map :
    FullFun.case (FullFun.pure.map Sum.inl) (FullFun.pure.map Sum.inr) =
      (FullFun.pure : FullFun E S (A ⊕ B) (A ⊕ B)) :=
  Silmaril.Proofs.Games.Abstract.FullFun.case_pure_map

/-- Sequencing distributes over copairing on the left. -/
theorem FullFun.seq_case {D : Type u} (g : FullFun E S A C) (h : FullFun E S B C)
    (k : FullFun E S C D) :
    FullFun.seq (FullFun.case g h) k = FullFun.case (FullFun.seq g k) (FullFun.seq h k) :=
  Prod.ext (AFun.seq_case g.1 h.1 k.1) (funext fun _ => funext fun x => by cases x <;> rfl)

/-- **The fixpoint law**: one iteration, then exit (`inl`) or iterate again (`inr`); finite
behaviours and productive runs. -/
theorem FullFun.iter_unfold (F : FullFun E S A (B ⊕ A)) :
    FullFun.iter F = FullFun.seq F (FullFun.case FullFun.pure (FullFun.iter F)) :=
  Prod.ext (AFun.iter_unfold F.1) (Silmaril.Proofs.Games.Abstract.FullFun.iter_unfold_inf F)

/-! ## Pure maps and whiskering -/

variable {D : Type u}

/-- The finite behaviours of a pure post-composition. -/
theorem FullFun.mem_map (f : FullFun E S A B) (h : B → C) (s : S) (a : A)
    (x : CallBeh E S C) :
    x ∈ (f.map h).1 s a ↔ ∃ c e, (c, e) ∈ f.1 s a ∧ x = (c, FullFun.endMap h e) :=
  Silmaril.Proofs.Games.Abstract.FullFun.mem_map f h s a x

/-- The productive runs of a pure post-composition are those of the original. -/
theorem FullFun.map_inf (f : FullFun E S A B) (h : B → C) : (f.map h).2 = f.2 := rfl

/-- Post-composition with the identity. -/
theorem FullFun.map_id (f : FullFun E S A B) : f.map id = f :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_id f

/-- Post-composition is functorial. -/
theorem FullFun.map_map (f : FullFun E S A B) (h : B → C) (h' : C → D) :
    (f.map h).map h' = f.map (h' ∘ h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_map f h h'

/-- Pre-composition with the identity. -/
theorem FullFun.comap_id (f : FullFun E S A B) : f.comap id = f := rfl

/-- Pre-composition is functorial. -/
theorem FullFun.comap_comap {A' A'' : Type u} (f : FullFun E S A B) (k : A' → A)
    (k' : A'' → A') : (f.comap k).comap k' = f.comap (k ∘ k') := rfl

/-- Pre- and post-composition commute. -/
theorem FullFun.map_comap {A' : Type u} (f : FullFun E S A B) (k : A' → A) (h : B → C) :
    (f.comap k).map h = (f.map h).comap k := rfl

/-- Sequencing with a pure map is that map. -/
theorem FullFun.seq_pure_map (f : FullFun E S A B) (h : B → C) :
    FullFun.seq f (FullFun.pure.map h) = f.map h :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_pure_map f h

/-- Sequencing after a pure map is pre-composition. -/
theorem FullFun.pure_map_seq (h : A → B) (g : FullFun E S B C) :
    FullFun.seq (FullFun.pure.map h) g = g.comap h :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_map_seq h g

/-- A pure map can be moved across sequencing. -/
theorem FullFun.seq_map (f : FullFun E S A B) (h : B → C) (g : FullFun E S C D) :
    FullFun.seq (f.map h) g = FullFun.seq f (g.comap h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_map f h g

/-- A pure map after a sequence is a pure map after its second part. -/
theorem FullFun.map_seq (f : FullFun E S A B) (g : FullFun E S B C) (h : C → D) :
    (FullFun.seq f g).map h = FullFun.seq f (g.map h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_seq f g h

/-- Pre-composition of a sequence is pre-composition of its first part. -/
theorem FullFun.comap_seq {A' : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (k : A' → A) : (FullFun.seq f g).comap k = FullFun.seq (f.comap k) g := rfl

/-- Right whiskering preserves the identity. -/
theorem FullFun.whiskerRight_pure :
    (FullFun.pure : FullFun E S A A).whiskerRight C = FullFun.pure :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_pure

/-- **Right whiskering preserves sequencing.** -/
theorem FullFun.whiskerRight_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerRight C = FullFun.seq (f.whiskerRight C) (g.whiskerRight C) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_seq f g C

/-- Left whiskering preserves the identity. -/
theorem FullFun.whiskerLeft_pure :
    (FullFun.pure : FullFun E S A A).whiskerLeft C = FullFun.pure :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_pure

/-- **Left whiskering preserves sequencing.** -/
theorem FullFun.whiskerLeft_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerLeft C = FullFun.seq (f.whiskerLeft C) (g.whiskerLeft C) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_seq f g C

/-- Right whiskering of a pure map is a pure map. -/
theorem FullFun.whiskerRight_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerRight C =
      FullFun.pure.map (Prod.map h id) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_pure_map h C

/-- Left whiskering of a pure map is a pure map. -/
theorem FullFun.whiskerLeft_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerLeft C =
      FullFun.pure.map (Prod.map id h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_pure_map h C

/-- **Interchange when the first component is a pure map.** -/
theorem FullFun.interchange_pure_left (h : A → B) (g : FullFun E S C D) :
    FullFun.seq (((FullFun.pure : FullFun E S A A).map h).whiskerRight C) (g.whiskerLeft B) =
      FullFun.seq (g.whiskerLeft A)
        (((FullFun.pure : FullFun E S A A).map h).whiskerRight D) :=
  Silmaril.Proofs.Games.Abstract.FullFun.interchange_pure_left h g

/-- **Interchange when the second component is a pure map.** -/
theorem FullFun.interchange_pure_right (f : FullFun E S A B) (k : C → D) :
    FullFun.seq (f.whiskerRight C) (((FullFun.pure : FullFun E S C C).map k).whiskerLeft B) =
      FullFun.seq (((FullFun.pure : FullFun E S C C).map k).whiskerLeft A)
        (f.whiskerRight D) :=
  Silmaril.Proofs.Games.Abstract.FullFun.interchange_pure_right f k

/-- **The interchange law fails** for effectful functions: with two operations, each with one
answer, calling `true` on the first component and `false` on the second gives the log
`[true, false]` in one order and `[false, true]` in the other. -/
theorem FullFun.not_interchange :
    ∃ (E : Sig.{0}) (f g : FullFun E PUnit PUnit PUnit),
      FullFun.seq (f.whiskerRight PUnit) (g.whiskerLeft PUnit) ≠
        FullFun.seq (g.whiskerLeft PUnit) (f.whiskerRight PUnit) :=
  ⟨_, _, _, Silmaril.Proofs.Games.Abstract.FullFun.not_interchange⟩

/-! ## Naturality and uniformity of iteration -/

/-- Mapping the exit value keeps the continuing chains. -/
theorem FullFun.contChain_map (F : FullFun E S A (B ⊕ A)) (h : B → C) {s : S} {a : A}
    {c : List (Call E)} {s' : S} {a' : A} :
    FullFun.ContChain (F.map (Sum.map h id)).1 s a c s' a' ↔ FullFun.ContChain F.1 s a c s' a' :=
  Silmaril.Proofs.Games.Abstract.FullFun.contChain_map

/-- **Naturality of iteration in the output**, finite behaviours: applying `h` to the exit value
of every iteration is applying it to the result of the loop. -/
theorem FullFun.iter_map_fin (f : AFun E S A (B ⊕ A)) (h : B → C) :
    AFun.iter (fun s a => (fun x => (x.1, FullFun.endMap (Sum.map h id) x.2)) '' f s a) =
      fun s a => (fun x => (x.1, FullFun.endMap h x.2)) '' AFun.iter f s a :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_map_fin f h

/-- **Naturality of iteration in the output.** -/
theorem FullFun.iter_map (F : FullFun E S A (B ⊕ A)) (h : B → C) :
    FullFun.iter (F.map (Sum.map h id)) = (FullFun.iter F).map h :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_map F h

/-- **Uniformity of iteration**, finite behaviours: if the body `f` at `k a` is the body `g` at
`a` with `k` applied to continuing arguments, the loops agree. -/
theorem FullFun.iter_uniform_fin {A' : Type u} {f : AFun E S A (B ⊕ A)}
    {g : AFun E S A' (B ⊕ A')} (k : A' → A)
    (hfg : ∀ s a, f s (k a) = (fun x => (x.1, FullFun.endMap (Sum.map id k) x.2)) '' g s a)
    (s : S) (a : A') : AFun.iter f s (k a) = AFun.iter g s a :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_uniform_fin hfg s a

/-- Under the uniformity hypothesis, a continuing chain of `G` maps to one of `F`. -/
theorem FullFun.contChain_uniform {A' : Type u} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} {k : A' → A} (hFG : F.comap k = G.map (Sum.map id k))
    {s : S} {a : A'} {c : List (Call E)} {s' : S} {a' : A'}
    (hc : FullFun.ContChain G.1 s a c s' a') : FullFun.ContChain F.1 s (k a) c s' (k a') :=
  Silmaril.Proofs.Games.Abstract.FullFun.contChain_uniform
    (Silmaril.Proofs.Games.Abstract.FullFun.fin_of_comap hFG) hc

/-- Under the uniformity hypothesis, a continuing chain of `F` from `k a` lifts to one of `G`
from `a`. -/
theorem FullFun.contChain_lift {A' : Type u} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} {k : A' → A} (hFG : F.comap k = G.map (Sum.map id k))
    {s : S} {a : A'} {c : List (Call E)} {s' : S} {x' : A}
    (hc : FullFun.ContChain F.1 s (k a) c s' x') :
    ∃ a', k a' = x' ∧ FullFun.ContChain G.1 s a c s' a' :=
  Silmaril.Proofs.Games.Abstract.FullFun.contChain_lift
    (Silmaril.Proofs.Games.Abstract.FullFun.fin_of_comap hFG) hc a rfl

/-- **Uniformity of iteration** with respect to a pure map `k`, pre-composition form. -/
theorem FullFun.iter_uniform_comap {A' : Type u} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} {k : A' → A} (hFG : F.comap k = G.map (Sum.map id k)) :
    (FullFun.iter F).comap k = FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_uniform_comap hFG

/-- The copairing of pure maps is a pure map. -/
theorem FullFun.case_pure_map_map {X : Type u} (h₁ : A → X) (h₂ : B → X) :
    FullFun.case ((FullFun.pure : FullFun E S A A).map h₁)
        ((FullFun.pure : FullFun E S B B).map h₂) =
      (FullFun.pure : FullFun E S (A ⊕ B) (A ⊕ B)).map (Sum.elim h₁ h₂) :=
  Silmaril.Proofs.Games.Abstract.FullFun.case_pure_map_map h₁ h₂

/-- **Uniformity of iteration** (Elgot form) for a pure map `h`: if `h ; F = G ; [inl, inr ∘ h]`
then `h ; iter F = iter G`. -/
theorem FullFun.iter_uniform {A' : Type u} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} (h : A' → A)
    (hFG : FullFun.seq (FullFun.pure.map h) F =
      FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (FullFun.pure.map (Sum.inr ∘ h)))) :
    FullFun.seq (FullFun.pure.map h) (FullFun.iter F) = FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_uniform h hFG

/-- **Dinaturality of iteration**: for `f : A → B ⊕ C` and `g : C → B ⊕ A`,
`iter (f ; [inl, g]) = f ; [id, iter (g ; [inl, f])]`. -/
theorem FullFun.iter_dinat (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ A)) :
    FullFun.iter (FullFun.seq f (FullFun.case (FullFun.pure.map Sum.inl) g)) =
      FullFun.seq f (FullFun.case FullFun.pure
        (FullFun.iter (FullFun.seq g (FullFun.case (FullFun.pure.map Sum.inl) f)))) :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_dinat f g

/-- **The codiagonal law**: for `F : A → (B ⊕ A) ⊕ A`, iterating twice is iterating once with
the two continue tags merged, `iter (iter F) = iter (F.map [id, inr])`. -/
theorem FullFun.iter_codiag (F : FullFun E S A ((B ⊕ A) ⊕ A)) :
    FullFun.iter (FullFun.iter F) = FullFun.iter (F.map (Sum.elim id Sum.inr)) :=
  Silmaril.Proofs.Games.Abstract.FullFun.iter_codiag F

/-- **Uniformity fails along a map that makes an import call**: `h` calls `x` and returns,
`G` continues silently; `h ; G = G ; [inl, inr ∘ h]` but `h ; iter G ≠ iter G`. -/
theorem FullFun.not_iter_uniform_call :
    ∃ (E : Sig.{0}) (x : Call E),
      let h : FullFun E PUnit PUnit PUnit := (fun s a => {([x], End.ret a s)}, fun _ _ => ∅)
      let G : FullFun E PUnit PUnit (PUnit ⊕ PUnit) := FullFun.pure.map Sum.inr
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
        FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G :=
  ⟨Silmaril.Proofs.Games.Abstract.FullFun.boolSig, ⟨true, ⟨⟩⟩,
    Silmaril.Proofs.Games.Abstract.FullFun.not_iter_uniform_call⟩

/-- **Uniformity fails along a map that traps**: `h` traps, `G` continues silently;
`h ; G = G ; [inl, inr ∘ h]` but `h ; iter G` traps while `iter G` diverges. -/
theorem FullFun.not_iter_uniform_trap :
    ∃ E : Sig.{0},
      let h : FullFun E PUnit PUnit PUnit := (fun _ _ => {([], End.trap)}, fun _ _ => ∅)
      let G : FullFun E PUnit PUnit (PUnit ⊕ PUnit) := FullFun.pure.map Sum.inr
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
        FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G :=
  ⟨_, Silmaril.Proofs.Games.Abstract.FullFun.not_iter_uniform_trap⟩

/-- Host preservation of post-composition: the same productive observations. -/
theorem hostObsInf_map {R : HostRel E} (f : FullFun E S A B) (h : B → C) :
    hostObsInf R (f.map h).2 = hostObsInf R f.2 := rfl

/-- Host preservation of pre-composition. -/
theorem hostObsInf_comap {A' : Type u} {R : HostRel E} (f : FullFun E S A B) (k : A' → A)
    (s : S) (a : A') : hostObsInf R (f.comap k).2 s a = hostObsInf R f.2 s (k a) := rfl

/-- Host preservation of right whiskering: the productive observations at `(a, c)` are those
at `a`. -/
theorem hostObsInf_whiskerRight {R : HostRel E} (f : FullFun E S A B) (s : S) (a : A) (c : C) :
    hostObsInf R (f.whiskerRight C).2 s (a, c) = hostObsInf R f.2 s a := rfl

/-- Host preservation of left whiskering: the productive observations at `(c, a)` are those
at `a`. -/
theorem hostObsInf_whiskerLeft {R : HostRel E} (f : FullFun E S A B) (s : S) (c : C) (a : A) :
    hostObsInf R (f.whiskerLeft C).2 s (c, a) = hostObsInf R f.2 s a := rfl

end Silmaril.Games.Abstract
