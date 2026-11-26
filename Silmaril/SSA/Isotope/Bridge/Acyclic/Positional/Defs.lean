module

public import Silmaril.Prelude.FiniteGraph.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms

/-! # Positional SSA tables with payload-only blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

open Silmaril.SSA.RVSDG.LambdaSSA
open LinearChain (Site localSite)

universe u

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- A single positional CFG table. Blocks may jump or case on a primitive
applied to their own parameter. Local targets may have multiple predecessors. -/
structure Table (Φ : Type u) [HasTy Φ τ] (L : LCtx τ) (n : Nat) where
  types : Fin n → τ
  block : ∀ i, Acyclic.Block Φ (List.ofFn types ++ L) (types i)

variable {L : LCtx τ} {n : Nat}

/-- Use the existing block target enumeration to check the supplied numbering.
All local edges strictly increase. External labels follow the locals. -/
def Table.check (p : Table Φ L n) : Bool :=
  (List.finRange n).all fun i => (p.block i).targets.all fun j => decide (i.val < j)

/-- A successful check certifies every edge, including edges of unreachable blocks. -/
abbrev Table.Forward (p : Table Φ L n) : Prop := p.check = true

/-- Keep precisely the targets in the local prefix. Exit labels remain in the
native typing and denotation, and are outside the dependency graph. -/
def Table.localTargets (p : Table Φ L n) (i : Fin n) : List (Fin n) :=
  (p.block i).targets.filterMap fun j => if h : j < n then some ⟨j, h⟩ else none

theorem Table.mem_localTargets (p : Table Φ L n) (i j : Fin n) :
    j ∈ p.localTargets i ↔ j.val ∈ (p.block i).targets := by
  simp only [localTargets, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, eq⟩
    split at eq
    · exact (congrArg Fin.val (Option.some.inj eq)) ▸ hk
    · contradiction
  · exact fun hj => ⟨j.val, hj, by simp [j.isLt]⟩

/-- A control edge with both endpoints in the local table. -/
def Table.LocalEdge (p : Table Φ L n) (i j : Fin n) : Prop :=
  j ∈ p.localTargets i

/-- A rank decreases at every transfer between local labels. -/
structure Ranking (p : Table Φ L n) where
  rank : Fin n → Nat
  decreases : ∀ i j, p.LocalEdge i j → rank j < rank i

/-- Check every local block, including blocks unreachable from a given entry. -/
def Table.checkAcyclic (p : Table Φ L n) : Bool :=
  FiniteGraph.kahn p.localTargets (List.finRange n)

/-- The successful check supplies the removal round of each local block. -/
def Table.acyclicRanking (p : Table Φ L n) (ok : p.checkAcyclic = true) : Ranking p where
  rank := FiniteGraph.krank p.localTargets (List.finRange n)
  decreases i j edge :=
    (FiniteGraph.kahn_sound p.localTargets (List.finRange n) ok).1
      i (List.mem_finRange i) j edge (List.mem_finRange j)

/-- Names in the native CFG have the local prefix followed by the ordered exits. -/
def Table.toSSA (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Region Φ :=
  .cfg (.br i (Morphism.CaseSSA.erase a.1)) n (fun j => (p.block j).region)

theorem Table.toSSA_hasType (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Region.HasType β.toList (p.toSSA i a) L :=
  .cfg p.types (.br (localSite p.types L i).typing (Morphism.CaseSSA.erase_hasType a.2.toHasType))
    (fun j => (p.block j).typing β.toList)

/-- Split a native target at the local/external boundary, retaining its payload type. -/
inductive Destination (p : Table Φ L n) (A : τ) where
  | local (i : Fin n) (ty : p.types i = A)
  | exit (j : Nat) (ty : At L j A)

/-- Classify a typed target by its position in the appended interface. -/
def Table.destination (p : Table Φ L n) {A : τ}
    (s : Site (List.ofFn p.types ++ L) A) : Destination p A :=
  if h : s.index < n then
    .local ⟨s.index, h⟩ (by
      have ty := s.typing
      change (List.ofFn p.types ++ L)[s.index]? = some A at ty
      rw [List.getElem?_append_left (by simpa using h)] at ty
      simpa [List.getElem?_eq_getElem, h] using ty)
  else
    .exit (s.index - n) (by
      have ty := s.typing
      change (List.ofFn p.types ++ L)[s.index]? = some A at ty
      rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)] at ty
      simpa only [List.length_ofFn] using ty)

/-- Apply a typed unary primitive to the newest payload. -/
def operand {d : Nat} {β : BoundCtx τ d} {A B : τ} (op : TwoBlock.Instruction Φ A B) :
    Operand Φ (β.snoc A) B := by
  obtain ⟨f, input, output⟩ := op
  subst A B
  exact ⟨.op f (.bv 0), .op .bv⟩

def Destination.index {p : Table Φ L n} {A : τ} : Destination p A → Nat
  | .local i _ => i.val
  | .exit j _ => n + j

theorem Table.destination_index (p : Table Φ L n) {A : τ}
    (s : Site (List.ofFn p.types ++ L) A) : (p.destination s).index = s.index := by
  unfold Table.destination
  split
  · rfl
  · rename_i h
    change n + (s.index - n) = s.index
    omega

theorem Table.forward_iff (p : Table Φ L n) :
    p.Forward ↔ ∀ i, ∀ j ∈ (p.block i).targets, i.val < j := by
  simp [Table.Forward, Table.check, List.all_eq_true]

/-- Reuse the existing ordered compiler's native block table. -/
def Table.ofCompiled {A : τ} (p : Acyclic.Compiled Φ L A) :
    Table Φ L (p.rest.locals.length + 1) :=
  ⟨p.localTypes, p.blockAt⟩

/-- The existing compiler's forward-edge theorem discharges this checker. -/
theorem Table.ofCompiled_forward {A : τ} (p : Acyclic.Compiled Φ L A) :
    (Table.ofCompiled p).Forward :=
  (Table.ofCompiled p).forward_iff.mpr p.blockAt_forward

/-- A forward-numbered table has a decreasing rank by reversing the numbering. -/
def Table.forwardRanking (p : Table Φ L n) (ok : p.Forward) : Ranking p where
  rank i := n - i.val
  decreases i j edge := by
    have := p.forward_iff.mp ok i j.val ((p.mem_localTargets i j).mp edge)
    omega

/-- A local continuation may be used under any surrounding context. Only the
newest payload is read by the source block. -/
abbrev LocalContinuations (p : Table Φ L n) (targets : List Nat) :=
  ∀ (j : Fin n), j.val ∈ targets → ∀ {d : Nat} (β : BoundCtx τ d),
    FiniteExit Φ L (β.snoc (p.types j))

def Table.compileDestination (p : Table Φ L n) {A : τ} {targets : List Nat}
    (target : Destination p A) (edge : target.index ∈ targets) {d : Nat} (β : BoundCtx τ d)
    (next : LocalContinuations p targets) : FiniteExit Φ L (β.snoc A) :=
  match target with
  | .local j ty => ty ▸ next j edge β
  | .exit _ ty => .br ty ⟨.bv 0, .bv⟩

def Table.compileTarget (p : Table Φ L n) {A : τ} {targets : List Nat}
    (s : Site (List.ofFn p.types ++ L) A) (edge : s.index ∈ targets) {d : Nat} (β : BoundCtx τ d)
    (next : LocalContinuations p targets) : FiniteExit Φ L (β.snoc A) :=
  p.compileDestination (p.destination s) ((p.destination_index s).symm ▸ edge) β next

def Table.compileBlock (p : Table Φ L n) (i : Fin n)
    (b : Acyclic.Block Φ (List.ofFn p.types ++ L) (p.types i)) {d : Nat} (β : BoundCtx τ d)
    (next : LocalContinuations p b.targets) : FiniteExit Φ L (β.snoc (p.types i)) :=
  match b with
  | .jump op s =>
    .join (.br (operand op)) (p.compileTarget s (by simp [Acyclic.Block.targets])
      (β.snoc (p.types i)) next)
  | .branch op l r =>
    .case (operand op)
      (p.compileTarget l (by simp [Acyclic.Block.targets]) (β.snoc (p.types i)) next)
      (p.compileTarget r (by simp [Acyclic.Block.targets]) (β.snoc (p.types i)) next)

/-- Unfold the local calls by decreasing rank, leaving the original numbering
and ordered exits intact. Shared blocks can be copied into several branches. -/
def Table.compileRankedAt (p : Table Φ L n) (ranking : Ranking p) (i : Fin n) {d : Nat}
    (β : BoundCtx τ d) : FiniteExit Φ L (β.snoc (p.types i)) :=
  p.compileBlock i (p.block i) β (fun j _ _ γ => p.compileRankedAt ranking j γ)
termination_by ranking.rank i
decreasing_by exact ranking.decreases i j ((p.mem_localTargets i j).mpr ‹j.val ∈ _›)

/-- Evaluate the entry operand once, then unfold the ranked table. -/
def Table.toFiniteExitRanked (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    FiniteExit Φ L β :=
  .join (.br a) (p.compileRankedAt ranking i β)

/-- Compile a ranked table through the exact finite-exit bridge. -/
def Table.toLetCaseRanked (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    Operand Φ β (Region.packedExitType L) :=
  (p.toFiniteExitRanked ranking i a).encode.toLetCase

/-- Check the original table and compile to exact LetCase when it is acyclic. -/
def Table.toLetCase? (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Option (Operand Φ β (Region.packedExitType L)) :=
  if h : p.checkAcyclic = true then some (p.toLetCaseRanked (p.acyclicRanking h) i a) else none

/-- The forward-numbered API uses the same rank-based unfolding. -/
def Table.compileAt (p : Table Φ L n) (ok : p.Forward) (i : Fin n) {d : Nat}
    (β : BoundCtx τ d) : FiniteExit Φ L (β.snoc (p.types i)) :=
  p.compileRankedAt (p.forwardRanking ok) i β

/-- Evaluate the entry operand, then use its value once as the first block
parameter. The output interface is the original ordered list of exits. -/
def Table.toFiniteExit (p : Table Φ L n) (ok : p.Forward) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : FiniteExit Φ L β :=
  p.toFiniteExitRanked (p.forwardRanking ok) i a

/-- Use the finite-exit bridge to produce exact LetCase. -/
def Table.toLetCase (p : Table Φ L n) (ok : p.Forward) {d : Nat} {β : BoundCtx τ d} (i : Fin n)
    (a : Operand Φ β (p.types i)) : Operand Φ β (Region.packedExitType L) :=
  p.toLetCaseRanked (p.forwardRanking ok) i a

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional
