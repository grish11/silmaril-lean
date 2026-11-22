module

import Silmaril.Formats.Dasl.Wire.Profile.Thms
import Silmaril.Formats.PER.Dense.Parent.Thms
import Silmaril.Formats.PER.UnionFind.Thms
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs
meta import Silmaril.Formats.Dasl.Encode.Thms
meta import Silmaril.Formats.PER.Dense.Parent.Thms
meta import Silmaril.Formats.PER.UnionFind.Thms

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.PER
open Silmaril.Formats.PER.Dense

namespace Silmaril.Formats.PER.DenseExamples

private def descending {size : Nat} (parent : Fin size → Option (Fin size)) (key next : Fin size) : Bool :=
  !(decide (parent key = some next ∧ key ≠ next)) || decide (next.val < key.val)

private theorem terminates {size : Nat} {parent : Fin size → Option (Fin size)}
    (tested : ∀ key next, descending parent key next = true) : WellFounded (fun next key => Parent.Step parent key next) := by
  apply Subrelation.wf _ (measure Fin.val).wf
  intro next key step
  change next.val < key.val
  simpa [descending, show parent key = some next ∧ key ≠ next from step] using tested key next

private def chain : Pointers.Checked (fun _ => Nat) := ⟨Pointers.ofList Index.nat [0, 0, 1], by decide⟩

private theorem chainForest : Parent.FixedForest chain.parent := by
  have known : ∀ key, (chain.parent key).isSome = true := by decide
  have tested : ∀ key next : Fin 3, descending (size := 3) chain.parent key next = true := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]; decide
  exact ⟨fun _ next _ => known next, terminates tested⟩

example : (chain.per .fixedPoint).rel (0 : Fin 3) (2 : Fin 3) := by
  change (Parent.partition .fixedPoint chain.parent).rel (0 : Fin 3) (2 : Fin 3)
  rw [fixed_eq_connectivity chainForest]
  exact (Parent.connectivity chain.parent).laws.trans
    ((Parent.connectivity chain.parent).laws.symm (Parent.edge_connected (key := (1 : Fin 3)) (next := (0 : Fin 3)) rfl))
    ((Parent.connectivity chain.parent).laws.symm (Parent.edge_connected (key := (2 : Fin 3)) (next := (1 : Fin 3)) rfl))

example : ¬ (chain.per .direct).rel (0 : Fin 3) (2 : Fin 3) := by
  rintro ⟨_, first, second⟩
  have different : (0 : Fin 3) ≠ 1 := by decide
  exact different (Option.some.inj (first.trans second.symm))

private def finiteRows : Table (fun size => Option (Fin size)) := ⟨3, [none, some 0, some 1], rfl⟩

example : (Pointers.ofFin finiteRows).Valid := Pointers.ofFin_valid finiteRows

example : (Pointers.ofFinTotal ⟨3, [0, 0, 1], rfl⟩).Valid := Pointers.ofFinTotal_valid _

private def missing : Pointers.Checked (fun _ => Nat) :=
  ⟨Pointers.ofSentinel Index.nat 99 [99, 0, 0], by decide⟩

private theorem missingForest : Parent.MissingForest missing.parent := by
  have noLoop : ∀ key, missing.parent key ≠ some key := by decide
  have tested : ∀ key next : Fin 3, descending (size := 3) missing.parent key next = true := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]; decide
  exact ⟨noLoop, terminates tested⟩

example : (missing.per .terminalMissing).rel (1 : Fin 3) (2 : Fin 3) := by
  change (Parent.partition .terminalMissing missing.parent).rel (1 : Fin 3) (2 : Fin 3)
  rw [missing_eq_connectivity_on_keys missingForest]
  exact ⟨rfl, rfl, (Parent.connectivity missing.parent).laws.trans
    (Parent.edge_connected (key := (1 : Fin 3)) (next := (0 : Fin 3)) rfl)
    ((Parent.connectivity missing.parent).laws.symm (Parent.edge_connected (key := (2 : Fin 3)) (next := (0 : Fin 3)) rfl))⟩

example : ¬ (missing.per .terminalMissing).Dom (0 : Fin 3) := by
  intro present
  have impossible : false = true := (Parent.missing_dom missingForest (0 : Fin 3)).mp present
  cases impossible

private def twoTerminals : Pointers.Checked (fun _ => Option Nat) :=
  ⟨Pointers.ofOptional Index.nat [none, some 0, none, some 2], by decide⟩

example : ¬ (twoTerminals.per .terminalMissing).rel (1 : Fin 4) (3 : Fin 4) := by
  intro related
  obtain ⟨root, left, right⟩ := (Parent.rel_iff (mode := .terminalMissing) (parent := twoTerminals.parent)
    (1 : Fin 4) (3 : Fin 4)).mp related
  have first : Parent.Roots .terminalMissing twoTerminals.parent (1 : Fin 4) (0 : Fin 4) :=
    ⟨rfl, .next (child := (0 : Fin 4)) ⟨rfl, by decide⟩ (.stop rfl)⟩
  have second : Parent.Roots .terminalMissing twoTerminals.parent (3 : Fin 4) (2 : Fin 4) :=
    ⟨rfl, .next (child := (2 : Fin 4)) ⟨rfl, by decide⟩ (.stop rfl)⟩
  have zero : root = (0 : Fin 4) := Parent.roots_functional left first
  have two : root = (2 : Fin 4) := Parent.roots_functional right second
  exact (by decide : (0 : Fin 4) ≠ 2) (zero.symm.trans two)

private def cycle : Pointers.Checked (fun _ => Nat) := ⟨Pointers.ofList Index.nat [1, 0], by decide⟩

example : (cycle.per .connectivity).rel (0 : Fin 2) (1 : Fin 2) := Parent.edge_connected (parent := cycle.parent) rfl

example : ¬ (cycle.per .fixedPoint).Dom (0 : Fin 2) := by
  intro supported
  have noRoot : ∀ key, cycle.parent key ≠ some key := by decide
  obtain ⟨root, hit⟩ := (Parent.dom_iff (mode := .fixedPoint) (parent := cycle.parent) (0 : Fin 2)).mp supported
  exact noRoot root (Parent.root_terminal hit)

private def classify : Nat → Option (Option Nat)
  | 0 => some none
  | 1 => some (some 0)
  | _ => none

private def options := Pointers.strategy (Row := fun _ => Nat) .connectivity Index.optionNat

example : (options.per missing).rel none (some 0) :=
  ⟨(0 : Fin 3), (1 : Fin 3), rfl, rfl, (Parent.connectivity missing.parent).laws.symm (Parent.edge_connected rfl)⟩

example : ((options.pull classify).per missing).rel 0 1 :=
  ⟨none, some 0, rfl, rfl, (0 : Fin 3), (1 : Fin 3), rfl, rfl,
    (Parent.connectivity missing.parent).laws.symm (Parent.edge_connected rfl)⟩

private theorem keyUnknown : ¬ ((options.pull classify).per missing).Dom 2 := by
  intro supported
  obtain ⟨_, hit, _⟩ := (pull_dom (options.per missing) classify 2).mp supported
  cases hit

example : ¬ ((options.pull classify).total missing).r 2 3 := fun related =>
  (by decide : (2 : Nat) ≠ 3) ((completion_unknown _ keyUnknown).mp related)

example {Class : Type} (rows : List Class) (key : Nat) : (Strategy.direct.per rows).Dom key ↔ key < rows.length :=
  direct_dom rows key

example (state : UnionFind Nat) (encode : Bool → Option Nat) :
    ((Strategy.unionFind.pull encode).per state) = state.partition.decodePull encode := rfl

private def beforeUnion : UnionFind Nat := (UnionFind.singleton 0).insert 1

example {state : UnionFind Nat} (merged : beforeUnion.union 0 1 = some state) :
    ((Strategy.unionFind.pull fun key : Bool => some key.toNat).per state).rel false true := by
  have both := (beforeUnion.union_isSome 0 1).mp (merged ▸ rfl)
  exact ⟨0, 1, rfl, rfl, (UnionFind.union_rel_iff merged 0 1).mpr (.inr (.inl both))⟩

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkWire {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let layout : Encode.TotalCodec (List UInt64) (Shallow Name) := Encode.listOf Encode.bits
  let codec := profile.codec layout
  let some bytes := codec.encode? [0, 0, 1] | throw (IO.userError "could not encode dense list")
  let some rows := codec.decode? bytes | throw (IO.userError "could not decode dense list")
  let raw := Pointers.ofList Index.uint64 rows
  check ((raw.check?).isSome && (raw.observe 2).target?.map Fin.val == some 1) "checked UInt64 parent decoding"

#eval show IO Unit from do
  let raw := Pointers.ofOptional Index.uint32 [none, some 0, some 99]
  check (raw.observe 0 == .missing && raw.observe 2 == .invalid 99 && raw.observe 3 == .unknown) "distinct diagnostics"
  check (raw.check?.isNone) "do not interpret malformed pointers as missing terminals"
  check (raw.table.toMap.lookup? 0 == some none && raw.table.toMap.lookup? 3 == none) "map keeps missing row as data"
  check ((Index.uint32.ofNat? (2^32)).isNone && (Index.uint64.ofNat? (2^64)).isNone) "reject overflow, do not wrap"
  let some merged := beforeUnion.union 0 1 | throw (IO.userError "union unexpectedly missed a supported key")
  check (merged.sameClass 0 1 == some true && merged.sameClass 0 2 == none) "union keeps unknown distinct"
  checkWire Wire.Profile.dasl
  checkWire Wire.Profile.bdasl

end Silmaril.Formats.PER.DenseExamples
