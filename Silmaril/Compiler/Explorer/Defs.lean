module

public import Silmaril.Compiler.CompilesTo.Sim.Defs

/-!
# Compilation problems, segment mappings and comorphism-generated relations

The vocabulary behind a *verified compiler explorer*: a source program on the left, target code
on the right, a many-to-many mapping between their fragments, and separate questions about it.
`docs/projects/compiler-explorer.md` is the guide.

Everything here is a thin, generic layer over the cut-point simulation of
`Silmaril.Compiler.CompilesTo.Sim` (`Source`, `Corr`, `Corr.Segment`, `Corr.Whole`); it does not
introduce a second semantics. A concrete instance (C functions, Cerberus Core and x86-64) is
`Silmaril.Project.CompilesTo.Explorer`.

## Four independent questions

1. **The translation** (`Problem.Valid`): from every entry the *calling convention* (`entry`, the
   ABI) relates, if the source cannot go wrong and terminates, the target returns with a result
   the source can produce. It mentions no mapping.
2. **One mapping edge** (`Mapping.EdgeValid M k`): the segment from program point `k` is
   simulated (`Corr.Segment`).
3. **The whole mapping** (`Mapping.Valid M`): every segment, *including the points nobody
   listed*, is simulated. A list of individually valid edges is not a valid mapping:
   `Mapping.valid_of_edges` needs coverage (`Mapping.Covers`), and `Counterexample.edges_not_valid`
   (in `Thms`) exhibits valid listed edges whose problem is not valid. A valid mapping that starts
   at the entry (`Mapping.Starts`) proves the translation (`Problem.valid_of_mapping`).
4. **Refinement of a generated relation** (`Mapping.RefinesAt`, `Mapping.RefinesComorphism`): the
   mapping's point relation implies the relation that a comorphism of observations (for C and
   x86: the DWARF locations of C objects) generates. This is a separate statement: a mapping can
   be valid without refining a given comorphism relation, and conversely.

## Directions

* **Refinement of programs.** `Problem.Valid` is a forward simulation from a safe source state.
  The target here is a *deterministic* machine (`τ → Option τ`), so its run from an entry is
  unique and the statement says that this run returns with a result some source run produces:
  the target *refines* the source (its one behaviour is among the source's). A nondeterministic
  or multithreaded target needs a backward statement over all its runs; that is not provided here
  (see the guide).
* **Refinement of relations.** `M.RefinesAt G K` reads "the mapping's relation is at least as
  strong as `G` at the points `K`" (`M.rel k ⊆ G k`). Strengthening the entry relation and
  weakening the result relation keeps a translation valid (`Problem.Valid.mono`).

## Undefined behaviour, divergence, I/O, concurrency

* Source undefined behaviour (`Source.wrong`) permits every target behaviour: every statement
  assumes `Source.Safe`, which also requires that *every* source run terminates. Divergent
  sources are therefore not covered.
* Source nondeterminism is handled by the existential over source runs.
* I/O is whatever the two semantics and the `result` relation observe; there is no separate trace
  of events. Concurrency is not modelled: one deterministic target thread.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

open Silmaril.Compiler.CompilesTo (Source Corr Seg)

universe u

variable {σ τ R : Type}

/-! ## The compilation problem -/

/-- **A compilation problem**: what it means for target code to implement a source program,
independently of any mapping between their fragments.

* `src`: the source execution model (its steps, undefined behaviour and results);
* `tgt`: the target execution model, a deterministic machine;
* `entry x0 s`: the calling convention (the ABI): the target entry state `x0` corresponds to the
  source start state `s`;
* `tgtFinal x0 x`: the target has returned from the call entered in `x0`;
* `result x0 r x`: the returned target state `x` corresponds to the source result `r`. -/
structure Problem (σ τ R : Type) where
  src : Source σ R
  tgt : τ → Option τ
  entry : τ → σ → Prop
  tgtFinal : τ → τ → Prop
  result : τ → R → τ → Prop

namespace Problem

variable (P : Problem σ τ R)

/-- The target's step relation. -/
def tgtStep (x y : τ) : Prop := P.tgt x = some y

/-- **The translation is valid**: from every entry the convention relates, if the source cannot
go wrong and every source run terminates, some source run ends with a result `r` and the target
run returns in a state that corresponds to `r`. -/
def Valid : Prop :=
  ∀ x0 s, P.entry x0 s → P.src.Safe s →
    ∃ t r y, Relation.ReflTransGen P.src.step s t ∧ P.src.final t r ∧
      Relation.ReflTransGen P.tgtStep x0 y ∧ P.tgtFinal x0 y ∧ P.result x0 r y

/-- **Not vacuous**: some entry has a safe source. A valid problem whose source is never safe
says nothing; this is a separate obligation. -/
def Inhabited : Prop := ∃ x0 s, P.entry x0 s ∧ P.src.Safe s

end Problem

/-! ## Segment mappings -/

/-- **A segment mapping** of a problem: numbered program points shared by the source and the
target, with the source states (`srcAt`) and target states (`tgtAt`) at each point and the
relation between them (`rel k x0 s x`, relative to the target entry `x0`). Point `0` is meant to
be the entry. -/
structure Mapping (P : Problem σ τ R) where
  srcAt : Nat → σ → Prop
  tgtAt : Nat → τ → Prop
  rel : Nat → τ → σ → τ → Prop

namespace Mapping

variable {P : Problem σ τ R} (M : Mapping P)

/-- The cut-point correspondence of the mapping (`Silmaril.Compiler.CompilesTo.Corr`). -/
def corr : Corr σ τ R where
  src := P.src
  tgt := P.tgt
  srcAt := M.srcAt
  tgtAt := M.tgtAt
  rel := M.rel
  tgtFinal := P.tgtFinal
  result := P.result

/-- **The mapping starts at the entry**: the convention's entry states are at point `0` and
related there. -/
def Starts : Prop :=
  ∀ x0 s, P.entry x0 s → M.srcAt 0 s ∧ M.tgtAt 0 x0 ∧ M.rel 0 x0 s x0

/-- **One edge is valid**: the segment from point `k` is simulated (`Corr.Segment`). -/
def EdgeValid (k : Nat) : Prop := M.corr.Segment k

/-- **The whole mapping is valid**: every segment is simulated, at every point number. -/
def Valid : Prop := ∀ k, M.EdgeValid k

/-- **The listed points cover the mapping**: at a point outside `L` no states are related, so
its segment is vacuous. Coverage is what turns valid listed edges into a valid mapping. -/
def Covers (L : List Nat) : Prop :=
  ∀ k, k ∉ L → ∀ x0 s x, M.srcAt k s → M.tgtAt k x → ¬ M.rel k x0 s x

/-! ### Relations between mappings and generated relations -/

/-- **The mapping refines `G` at the points `K`**: at each point of `K` its relation implies
`G` (it is at least as strong). -/
def RefinesAt (G : Nat → τ → σ → τ → Prop) (K : Nat → Prop) : Prop :=
  ∀ k, K k → ∀ x0 s x, M.rel k x0 s x → G k x0 s x

end Mapping

/-! ## Observation logics and their comorphisms -/

/-- **A logic of observations** over states `S`: observables `Obs` and their values `V`;
`Holds s o v` says that in `s` the observable `o` has the value `v`. The sentences are the
equations `o = v`. -/
structure ObsLogic (S V : Type) where
  Obs : Type
  Holds : S → Obs → V → Prop

/-- Each observable has at most one value in each state. -/
def ObsLogic.Functional {S V : Type} (L : ObsLogic S V) : Prop :=
  ∀ s o v w, L.Holds s o v → L.Holds s o w → v = w

/-- **A comorphism of observation logics**: the signature part of an institution comorphism
whose sentences are the equations `o = v`. Each source observable is read at a target observable
(for C and x86-64: each C object at its DWARF location), and the sentence `o = v` translates to
`map o = v`. There is no model translation: a target state does not determine a source state. -/
structure ObsComorphism {S T V : Type} (A : ObsLogic S V) (B : ObsLogic T V) where
  map : A.Obs → B.Obs

namespace ObsComorphism

variable {S T U V : Type} {A : ObsLogic S V} {B : ObsLogic T V} {C : ObsLogic U V}

/-- **The relation a comorphism generates** on the observables `Φ`: every observable of `Φ` has
a value that holds of it in `s` and of its translation in `x`. -/
def Generated (c : ObsComorphism A B) (Φ : A.Obs → Prop) (s : S) (x : T) : Prop :=
  ∀ o, Φ o → ∃ v, A.Holds s o v ∧ B.Holds x (c.map o) v

/-- The identity comorphism. -/
def id (A : ObsLogic S V) : ObsComorphism A A := ⟨fun o => o⟩

/-- Composition: read through `c`, then through `d`. -/
def comp (c : ObsComorphism A B) (d : ObsComorphism B C) : ObsComorphism A C :=
  ⟨fun o => d.map (c.map o)⟩

/-- The image of a set of observables. -/
def image (c : ObsComorphism A B) (Φ : A.Obs → Prop) : B.Obs → Prop :=
  fun o' => ∃ o, Φ o ∧ c.map o = o'

end ObsComorphism

namespace Mapping

variable {P : Problem σ τ R}

/-- **The mapping refines the relation a comorphism generates**: at each point of `K`, the
observables `scope k` of a related source state `s` and target state `x` (read relative to the
entry `x0`, as frame-relative locations are) have common values. -/
def RefinesComorphism {V : Type} (M : Mapping P) {A : ObsLogic σ V} {B : ObsLogic (τ × τ) V}
    (c : ObsComorphism A B) (scope : Nat → A.Obs → Prop) (K : Nat → Prop) : Prop :=
  M.RefinesAt (fun k x0 s x => c.Generated (scope k) s (x0, x)) K

/-- **The mapping a comorphism generates** (the usual construction): at point `k`, an extra
relation `frame k` (control, stack discipline) and the comorphism's relation on `scope k`. -/
def ofComorphism {V : Type} {A : ObsLogic σ V} {B : ObsLogic (τ × τ) V}
    (srcAt : Nat → σ → Prop) (tgtAt : Nat → τ → Prop) (frame : Nat → τ → σ → τ → Prop)
    (c : ObsComorphism A B) (scope : Nat → A.Obs → Prop) : Mapping P where
  srcAt := srcAt
  tgtAt := tgtAt
  rel k x0 s x := frame k x0 s x ∧ c.Generated (scope k) s (x0, x)

end Mapping

/-! ## Identities and provenance (data, outside the statements)

What the statements are *about* is fixed by the Lean terms above. The records below name those
terms and the artifacts they were built from, for the explorer's database. They carry no proof
and confer no status. -/

/-- How the target relates to the source artifact. -/
inductive Direction where
  /-- The target was produced from the source by a compiler. -/
  | compiled
  /-- The source was produced from the target by a decompiler. -/
  | decompiled
  /-- Both were supplied, with no recorded derivation. -/
  | imported
  deriving Repr, DecidableEq

/-- A model or convention, by the Lean declaration that defines it and a version. -/
structure ModelRef where
  family : String
  decl : String
  version : String
  deriving Repr, DecidableEq

/-- An immutable artifact: its role, its SHA-256 (lowercase hex) and size in bytes. -/
structure ArtifactRef where
  role : String
  sha256 : String
  size : Nat
  deriving Repr, DecidableEq

end Silmaril.Compiler.Explorer

end
