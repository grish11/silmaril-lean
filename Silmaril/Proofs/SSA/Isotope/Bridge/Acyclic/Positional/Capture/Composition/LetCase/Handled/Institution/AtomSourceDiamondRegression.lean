module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Source.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation RankedEntry denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

set_option backward.isDefEq.respectTransparency false

/-! ## A written source diamond with a join before the stored reply is inspected

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `test` takes
one atom and replies with one of two tags, each carrying one atom. `echo`
and `mark` take one atom and reply with one atom. Two older atoms are
captured. The exits are a pair of atoms and one atom. -/

private inductive Op | pick | test | echo | mark
  deriving DecidableEq

local instance : TaggedSignature Unit Op where
  argument
    | .pick => .atom ()
    | .test => .atom ()
    | .echo => .atom ()
    | .mark => .atom ()
  first
    | .pick => [(), ()]
    | .test => [()]
    | .echo => [()]
    | .mark => [()]
  others
    | .pick => [[()]]
    | .test => [[()]]
    | .echo => []
    | .mark => []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev sumTy : Ty Unit := .coprod pairTy tok
private abbrev testTy : Ty Unit := .coprod tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev later : Slot older tok := ⟨0, rfl⟩

/-! ## The source graph

A flat acyclic graph of four rows over the two captures. It is written by
hand as a checked captured table. A row has one block parameter, reads the
captures and its parameter, and ends in a jump or a case. The reply `s` of
`pick` is live in every row, so it is passed in the packets: the packet of
rows 1 to 3 is a pair of an atom and `s`.

- Entry: ask `pick` on the later capture. Its reply `s` is the packet of
  row 0.
- Row 0, the classifier, with parameter `s`: ask `test` on the earlier
  capture and case on its reply. Under the first tag, with payload `a`,
  go to row 1 with `(a, s)`. Under the second tag, with payload `b`, go to
  row 2 with `(b, s)`.
- Row 1, the first predecessor, with parameter `(a, s)`: ask `echo` on
  `a`, with reply `e`, and jump to row 3 with `(e, s)`. This is the effect
  before the join, and `e` is the incoming join value.
- Row 2, the second predecessor, with parameter `(b, s)`: jump to row 3
  with its parameter. Its incoming join value is `b`.
- Row 3, the join, with parameter `(j, s)`. The parameter is the phi of
  the two incoming values. Ask `mark` on `j`, with reply `f`; then case on
  `s`. Under its first tag, with payload a pair, return the first
  component with `f`. Under its second tag, with payload `q`, return `q`
  with `j`. Both arms leave at the first exit.

Rows 1 and 2 are the two predecessors of row 3, and row 3 is written
once. -/

/-- The packet of rows 1 to 3: an atom and the stored reply. -/
private abbrev packet : Ty Unit := .product tok sumTy

private abbrev types : Fin 4 → Ty Unit := ![sumTy, packet, packet, packet]

private def entry : Operand Op older sumTy := ⟨.op .pick (.bv 0), .op .bv⟩

private def classifier : Operand Op (older.snoc sumTy) (.coprod packet packet) :=
  ⟨.let₁ (.op .test (.bv 2)) (.case (.bv 0) (.inl (.pair (.bv 0) (.bv 2))) (.inr (.pair (.bv 0) (.bv 2)))),
    .let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))⟩

/-- The first predecessor. It passes the reply of `echo` to the join. -/
private def predecessor : Operand Op (older.snoc packet) packet :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .echo (.bv 1)) (.pair (.bv 0) (.bv 1))),
    .let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))⟩

/-- The first predecessor with a changed incoming join value: it asks
`echo` as before and passes its own payload `a` to the join. -/
private def predecessorPayload : Operand Op (older.snoc packet) packet :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .echo (.bv 1)) (.pair (.bv 2) (.bv 1))),
    .let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))⟩

/-- The second predecessor passes its parameter on. -/
private def pass : Operand Op (older.snoc packet) packet := ⟨.bv 0, .bv⟩

/-- The join row: `mark` on the joined atom, then the case on the stored
reply. Its value leaves at the first exit. -/
private def joinRow : Operand Op (older.snoc packet) pairTy :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .mark (.bv 1))
      (.case (.bv 1) (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.pair (.bv 0) (.bv 3)))),
    .let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))⟩

/-- The table, with the operand of the first predecessor given. -/
private abbrev diamond (first : Operand Op (older.snoc packet) packet) : Table Op older exits 3 where
  types := types
  block := fun i =>
    Fin.cases (motive := fun j => Block Op older types exits (types j))
      (.case classifier (.local 1) (.local 2))
      (fun j => Fin.cases (motive := fun j => Block Op older types exits (types j.succ))
        (.jump first (.local 3))
        (fun j => Fin.cases (motive := fun j => Block Op older types exits (types j.succ.succ))
          (.jump pass (.local 3))
          (fun j => Fin.cases (motive := fun j => Block Op older types exits (types j.succ.succ.succ))
            (.jump joinRow (.exit (i := 0) rfl))
            (fun j => j.elim0) j) j) j) i

private theorem checked (first : Operand Op (older.snoc packet) packet) : (diamond first).check = true := by
  cbv

/-- The classifier goes to the two predecessors, both predecessors go to
the join, and the join leaves the graph. -/
example : (List.finRange 4).map (diamond predecessor).localTargets = [[1, 2], [3], [3], []] := rfl

/-- The source graph: entry at row 0, with the reply of `pick`. -/
private def source : CheckedTable Op older exits := ⟨3, diamond predecessor, checked predecessor, entry⟩

/-- The source graph with the changed predecessor. Only row 1 differs. -/
private def sourcePayload : CheckedTable Op older exits :=
  ⟨3, diamond predecessorPayload, checked predecessorPayload, entry⟩

/-! ## The checked readback

The readback unfolds the table from its entry. The join row is unfolded
once under each predecessor. -/

section Readback

variable (first : Operand Op (older.snoc packet) packet)

private theorem compile_join {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (diamond first).compileAt (checked first) 3 s =
      .join (.br (s.operand joinRow)) (.br (i := 0) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_first {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (diamond first).compileAt (checked first) 1 s =
      .join (.br (s.operand first)) ((diamond first).compileAt (checked first) 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_pass {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (diamond first).compileAt (checked first) 2 s =
      .join (.br (s.operand pass)) ((diamond first).compileAt (checked first) 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_classifier {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (diamond first).compileAt (checked first) 0 s =
      .case (s.operand classifier) ((diamond first).compileAt (checked first) 1 (.skip s sumTy))
        ((diamond first).compileAt (checked first) 2 (.skip s sumTy)) := by
  rw [Table.compileAt.eq_def]
  rfl

/-- The readback as a term of the unfolded rows. -/
private theorem readback_rows :
    ((diamond first).toLetCase (checked first) 0 entry).1 =
      (FiniteExit.join (Code.br entry)
        (FiniteExit.case (Scope.base.operand classifier)
          (FiniteExit.join (Code.br ((Scope.skip .base sumTy).operand first))
            (FiniteExit.join (Code.br ((Scope.skip (.skip .base sumTy) packet).operand joinRow))
              (FiniteExit.br (i := 0) rfl ⟨.bv 0, .bv⟩)))
          (FiniteExit.join (Code.br ((Scope.skip .base sumTy).operand pass))
            (FiniteExit.join (Code.br ((Scope.skip (.skip .base sumTy) packet).operand joinRow))
              (FiniteExit.br (i := 0) rfl ⟨.bv 0, .bv⟩)))) :
        FiniteExit Op exits older).encode.toLetCase.1 := by
  unfold Table.toLetCase Table.toFiniteExit
  rw [compile_classifier first .base, compile_first first (.skip .base sumTy),
    compile_pass first (.skip .base sumTy), compile_join first (.skip (.skip .base sumTy) packet)]

end Readback

/-- The term read back from the source graph. The request `pick` comes
first. The classifier is the scrutinee of a case, and the join row occurs
once in each arm, after the operand of the predecessor. -/
private abbrev readbackTerm : Term 2 :=
  (.let₁ (.op Op.pick (.bv 0))
    (.case (.let₁ (.op Op.test (.bv 2)) (.case (.bv 0) (.inl (.pair (.bv 0) (.bv 2))) (.inr (.pair (.bv 0) (.bv 2)))))
      (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 0) (.bv 1))))
        (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.pair (.bv 0) (.bv 3)))))
          (.inl (.bv 0))))
      (.let₁ (.bv 0)
        (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.pair (.bv 0) (.bv 3)))))
          (.inl (.bv 0))))))

private theorem source_readback : source.toLetCase.1 = readbackTerm :=
  (readback_rows predecessor).trans (by decide +kernel)

/-- The term read back from the source graph with the changed
predecessor. -/
private abbrev readbackPayloadTerm : Term 2 :=
  (.let₁ (.op Op.pick (.bv 0))
    (.case (.let₁ (.op Op.test (.bv 2)) (.case (.bv 0) (.inl (.pair (.bv 0) (.bv 2))) (.inr (.pair (.bv 0) (.bv 2)))))
      (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 2) (.bv 1))))
        (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.pair (.bv 0) (.bv 3)))))
          (.inl (.bv 0))))
      (.let₁ (.bv 0)
        (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.pair (.bv 0) (.bv 3)))))
          (.inl (.bv 0))))))

private theorem sourcePayload_readback : sourcePayload.toLetCase.1 = readbackPayloadTerm :=
  (readback_rows predecessorPayload).trans (by decide +kernel)

/-! ## The readback is natively a tree

The packets are removed by native laws. The case on the classifier is
turned into the request followed by the case on its reply; a let that
binds a pair of slots and the pattern let on that pair are removed; the
exit injection is moved into the two arms of the stored reply. The steps
are the sequencing laws, case beta at an injection, pure-let beta, and the
derived equation for a pattern let on a pair of slots. No request moves
past another request. -/

/-- The tree-shaped term: `pick`, `test`, the case on the reply of `test`,
`echo` under its first tag, and `mark` and the case on `s` in each arm. -/
private abbrev expandedTerm : Term 2 :=
  (.let₁ (.op Op.pick (.bv 0))
    (.let₁ (.op Op.test (.bv 2))
      (.case (.bv 0)
        (.let₁ (.op Op.echo (.bv 0))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 2))))))))

private theorem readback_expanded :
    Equiv false Γ₀ older readbackTerm expandedTerm (packedExitType exits) := by
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.bindLetCase .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false)
      (.inl (.pair .bv .bv)) (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))) (.refl (.let₁ (A := .coprod
      packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.caseBetaL (B := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (A :=
      .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv
      .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (A :=
      .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false) (.inr
      (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair
      .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair
      .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.caseBetaR (A := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁
      .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (let_pair_slots (0 : Fin 5) (2 : Fin 5) rfl rfl
      (.let₁ (.op .bv) (.pair .bv .bv))) (.refl (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂
      .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.refl
      (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv
      .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (let_pair_slots (0 :
      Fin 6) (3 : Fin 6) rfl rfl (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.refl (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv)
      (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv))))
      (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.bindLetCase .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv) (.inl .bv)))) (.refl (.let₁
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁
      (.pair .bv .bv) (.inl .bv)))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv
      .bv) (.pair .bv .bv) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.inl .bv)))))) (.refl (.let₁
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff :=
      false) (.pair .bv .bv) (.pair .bv .bv) (.inl .bv))))) (.refl (.let₁ (.pair .bv .bv) (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.letBeta (pureEff := false) (.pair
      .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv
      .bv)) (.pair .bv .bv)))) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (let_pair_slots (0 : Fin 5) (2
      : Fin 5) rfl rfl (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv))))
      (.refl (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.bindLet (.op .bv) (.case .bv (.let₂
      .bv (.pair .bv .bv)) (.pair .bv .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.bindLetCase .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (.pair .bv .bv)
      (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair
      .bv .bv) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.inl .bv))))))) ?_
  exact .refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₁ (.op .bv) (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv))))) (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))))

/-- The same term for the changed predecessor: `mark` takes the payload
`a`, and the second tag of `s` returns it. -/
private abbrev expandedPayloadTerm : Term 2 :=
  (.let₁ (.op Op.pick (.bv 0))
    (.let₁ (.op Op.test (.bv 2))
      (.case (.bv 0)
        (.let₁ (.op Op.echo (.bv 0))
          (.let₁ (.op Op.mark (.bv 1))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 3))))))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 2))))))))

private theorem readbackPayload_expanded :
    Equiv false Γ₀ older readbackPayloadTerm expandedPayloadTerm (packedExitType exits) := by
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.bindLetCase .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false)
      (.inl (.pair .bv .bv)) (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))) (.refl (.let₁ (A := .coprod
      packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.caseBetaL (B := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (A :=
      .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv
      .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (A :=
      .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false) (.inr
      (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair
      .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair
      .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.caseBetaR (A := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair
      .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.let₁ .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv
      .bv))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁
      .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (let_pair_slots (0 : Fin 5) (2 : Fin 5) rfl rfl
      (.let₁ (.op .bv) (.pair .bv .bv))) (.refl (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂
      .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))) (.refl
      (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv
      .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (let_pair_slots (1 :
      Fin 6) (3 : Fin 6) rfl rfl (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv
      .bv)))) (.refl (.inl .bv)))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv) (.case
      .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv)
      (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv))))
      (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.bindLetCase .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv) (.inl .bv)))) (.refl (.let₁
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁
      (.pair .bv .bv) (.inl .bv)))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv
      .bv) (.pair .bv .bv) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.inl .bv)))))) (.refl (.let₁
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv))
      (.pair .bv .bv)))) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.case (.refl .bv) (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff :=
      false) (.pair .bv .bv) (.pair .bv .bv) (.inl .bv))))) (.refl (.let₁ (.pair .bv .bv) (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv)))) (.inl
      .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.letBeta (pureEff := false) (.pair
      .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv
      .bv)) (.pair .bv .bv)))) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (let_pair_slots (0 : Fin 5) (2
      : Fin 5) rfl rfl (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv))))
      (.refl (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.bindLet (.op .bv) (.case .bv (.let₂
      .bv (.pair .bv .bv)) (.pair .bv .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv))
      (Equiv.bindLetCase .bv (.let₂ .bv (.pair .bv .bv)) (.pair .bv .bv) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (.pair .bv .bv)
      (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair
      .bv .bv) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op
      .bv)) (Equiv.case (.refl .bv) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv
      (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case
      (.refl .bv) (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.inl .bv))))))) ?_
  exact .refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₁ (.op .bv) (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv))))) (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))))

/-! ## The join node and its expansion

The same program as a join: under the stored reply, the reply of `test` is
cased on, the two arms supply one atom, and one continuation asks `mark`
on it and inspects the stored reply. -/

private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy
private abbrev underY : BoundCtx (Ty Unit) 4 := underS.snoc testTy
private abbrev arm : BoundCtx (Ty Unit) 5 := underY.snoc tok
private abbrev armE : BoundCtx (Ty Unit) 6 := arm.snoc tok
private abbrev afterMark : BoundCtx (Ty Unit) 6 := arm.snoc tok
private abbrev leafL : BoundCtx (Ty Unit) 9 := ((afterMark.snoc pairTy).snoc tok).snoc tok
private abbrev leafR : BoundCtx (Ty Unit) 7 := afterMark.snoc tok

/-- The first arm supplies the reply of `echo`. -/
private def leftReply : SpelledPrefix (Φ := Op) [[()]] arm (.cons ⟨0, rfl⟩ .nil) [[()]] armE
    (.cons ⟨0, rfl⟩ .nil) :=
  .ask Op.echo (.atom (β := arm) ⟨0, rfl⟩) (.bind [()] (.pick (.there .here) (.atom .stop)))

/-- The first arm supplies its payload. -/
private def leftPayload : SpelledPrefix (Φ := Op) [[()]] arm (.cons ⟨0, rfl⟩ .nil) [[()]] armE
    (.cons ⟨1, rfl⟩ .nil) :=
  .ask Op.echo (.atom (β := arm) ⟨0, rfl⟩) (.bind [()] (.atom .stop))

/-- The second arm supplies its payload and asks nothing. -/
private def rightArm : SpelledPrefix (Φ := Op) [[()]] arm (.cons ⟨0, rfl⟩ .nil) [[()]] arm
    (.cons ⟨0, rfl⟩ .nil) :=
  .stop

private def firstArm : SpelledStack (Φ := Op) [[(), ()]] (afterMark.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
    (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))) : Term 7) :=
  .step (.atom (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨3, rfl⟩)))))

private def secondArm : SpelledStack (Φ := Op) [[()]] leafR (.cons ⟨0, rfl⟩ .nil) exits
    (.inl (.pair (.bv 0) (.bv 2)) : Term 7) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩))))

/-- The continuation, written once. -/
private def continuation :
    SpelledDelay (Φ := Op) [(), ()] [()] [[()]] arm (.cons ⟨0, rfl⟩ .nil) 2 exits
      (.let₁ (.op Op.mark (.bv 0))
        (.case (.bv 3)
          (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
          (.inl (.pair (.bv 0) (.bv 2)))) : Term 5) :=
  .atom
    (.ask Op.mark (.atom (β := arm) ⟨0, rfl⟩)
      (.bind [()] (.atom (.inspect (Δ := afterMark) ⟨3, rfl⟩ firstArm secondArm))))

/-- The join node of the source graph. -/
private def join :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits
      (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 0)) (.bv 0))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 2))))) : Term 4) :=
  (SpelledJoinTags.join (atoms := [(), ()]) (next := [()]) (stack := []) (Δ := underS) (holds := .nil)
    (s := 0) (L := exits) [()] [()] [()] leftReply rfl rightArm rfl continuation :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits _)

/-- The join node of the source graph with the changed predecessor. -/
private def joinPayload :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits
      (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 1)) (.bv 0))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 2))))) : Term 4) :=
  (SpelledJoinTags.join (atoms := [(), ()]) (next := [()]) (stack := []) (Δ := underS) (holds := .nil)
    (s := 0) (L := exits) [()] [()] [()] leftPayload rfl rightArm rfl continuation :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits _)

/-- The whole term around a term under the reply of `test`. -/
private abbrev around (t : Term 4) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0)) (.let₁ (.op Op.test (.bv 2)) t)

/-- The native typing of the joined term. -/
private def joinedTyping {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits t) :
    Derivation Op Γ₀ older (around t) (packedExitType exits) :=
  .let₁ (.op (f := Op.pick) (argTyping (Assembly.atom later)))
    (.let₁ (.op (f := Op.test) (argTyping (Assembly.atom (β := underS) ⟨2, rfl⟩))) j.typing)

/-- The expansion of the join, as a tree of the grammar. -/
private def expanded {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits t) :
    Spelled older exits (around j.expand.term) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedTree (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (.ask Op.test (.atom (β := underS) ⟨2, rfl⟩) j.expand.tree)))

/-- The joined term is natively equal to its expansion. -/
private theorem joined_native {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [()]] underS .nil 0 exits t) :
    Equiv false Γ₀ older (around t) (around j.expand.term) (packedExitType exits) :=
  Equiv.let₁ (.refl (Derivation.op (f := Op.pick) (argTyping (Assembly.atom later))).toHasType)
    (Equiv.let₁
      (.refl (Derivation.op (f := Op.test) (argTyping (Assembly.atom (β := underS) ⟨2, rfl⟩))).toHasType)
      (spelledJoinTags_equiv_expand j))

/-- The term of the expansion of the join is the tree-shaped term reached
from the readback. -/
private theorem expanded_term : around join.expand.term = expandedTerm := by decide +kernel

private theorem expandedPayload_term : around joinPayload.expand.term = expandedPayloadTerm := by
  decide +kernel

/-! ## The source graph, the join and the expansion -/

/-- The readback of the source graph is natively equal to the expansion of
the join. -/
private theorem source_expanded :
    Equiv false Γ₀ older source.toLetCase.1 (around join.expand.term) (packedExitType exits) :=
  source_readback ▸ expanded_term ▸ readback_expanded

private theorem sourcePayload_expanded :
    Equiv false Γ₀ older sourcePayload.toLetCase.1 (around joinPayload.expand.term)
      (packedExitType exits) :=
  sourcePayload_readback ▸ expandedPayload_term ▸ readbackPayload_expanded

/-- The readback of the source graph is natively equal to the joined
term: a let whose bound term is the case on the reply of `test`, with the
continuation written once. -/
example : Equiv false Γ₀ older source.toLetCase.1
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 0)) (.bv 0))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2)
    (packedExitType exits) :=
  source_expanded.trans (joined_native join).symm

/-- The normal form with the chosen argument of `mark` under the first tag
of `test`, in both arms of `s`, and the chosen returned atom. -/
private abbrev normalWith (markL : Fin 9) (markR : Fin 7) (supplied : Fin 8) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.test (.bv 5))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₁ (.op Op.mark (.bv markL)) (.inl (.pair (.bv 5) (.bv 0)))))
            (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 4) (.bv 0)))))))
      (.let₁ (.op Op.test (.bv 3))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv markR)) (.inl (.pair (.bv 4) (.bv supplied)))))
          (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 3) (.bv 1)))))))

private theorem expanded_normal : ((expanded join).normal (.id older)).1 = normalWith 0 0 1 := by
  decide +kernel

private theorem expandedPayload_normal :
    ((expanded joinPayload).normal (.id older)).1 = normalWith 1 1 2 := by decide +kernel

/-- The readback of the source graph is natively equal to the #5304 normal
form of the join. -/
example : Equiv false Γ₀ older source.toLetCase.1 (normalWith 0 0 1) (packedExitType exits) :=
  source_expanded.trans (expanded_normal ▸ spelled_equiv_normal (expanded join))

/-! ## The eager spelling

The reply of `pick` is cased on at once and each of its arms is a tree
written by hand, without a join. -/

private abbrev eagerP : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev eagerPA : BoundCtx (Ty Unit) 6 := (eagerP.snoc testTy).snoc tok
private abbrev eagerPAe : BoundCtx (Ty Unit) 7 := eagerPA.snoc tok
private abbrev eagerPAleaf : BoundCtx (Ty Unit) 10 := ((eagerPAe.snoc tok).snoc tok).snoc tok
private abbrev eagerPBleaf : BoundCtx (Ty Unit) 9 := ((eagerPA.snoc tok).snoc tok).snoc tok
private abbrev eagerQ : BoundCtx (Ty Unit) 4 := underS.snoc tok
private abbrev eagerQA : BoundCtx (Ty Unit) 6 := (eagerQ.snoc testTy).snoc tok
private abbrev eagerQAe : BoundCtx (Ty Unit) 7 := eagerQA.snoc tok
private abbrev eagerQAleaf : BoundCtx (Ty Unit) 8 := eagerQAe.snoc tok
private abbrev eagerQBleaf : BoundCtx (Ty Unit) 7 := eagerQA.snoc tok

/-- The arm of the first tag of `s`. -/
private def eagerFirst :=
  SpelledStack.ask (L := exits) (stack := [[(), ()]]) (Δ := eagerP) (holds := .cons ⟨0, rfl⟩ .nil) Op.test
    (.atom (β := eagerP) ⟨3, rfl⟩)
    (.split [()] [()] []
      (.atom
        (.ask Op.echo (.atom (β := eagerPA) ⟨0, rfl⟩)
          (.bind [()]
            (.atom
              (.ask Op.mark (.atom (β := eagerPAe) ⟨0, rfl⟩)
                (.bind [()]
                  (.atom
                    (.step
                      (.atom
                        (.done (.ret pairExit (.pair (.atom (β := eagerPAleaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))))
      (.bind [()]
        (.atom
          (.ask Op.mark (.atom (β := eagerPA) ⟨0, rfl⟩)
            (.bind [()]
              (.atom
                (.step
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := eagerPBleaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))

/-- The arm of the second tag of `s`. -/
private def eagerSecond :=
  SpelledStack.ask (L := exits) (stack := [[()]]) (Δ := eagerQ) (holds := .cons ⟨0, rfl⟩ .nil) Op.test
    (.atom (β := eagerQ) ⟨3, rfl⟩)
    (.split [()] [()] []
      (.atom
        (.ask Op.echo (.atom (β := eagerQA) ⟨0, rfl⟩)
          (.bind [()]
            (.atom
              (.ask Op.mark (.atom (β := eagerQAe) ⟨0, rfl⟩)
                (.bind [()]
                  (.atom
                    (.atom
                      (.done (.ret pairExit (.pair (.atom (β := eagerQAleaf) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))
      (.bind [()]
        (.atom
          (.ask Op.mark (.atom (β := eagerQA) ⟨0, rfl⟩)
            (.bind [()]
              (.atom
                (.atom
                  (.done (.ret pairExit (.pair (.atom (β := eagerQBleaf) ⟨3, rfl⟩) (.atom ⟨1, rfl⟩)))))))))))

private def eager :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (.split (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] eagerFirst (.bind [()] eagerSecond)))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 0 0 1 := by decide +kernel

/-! ## Ranked validity and ordered-exit arrows of the source graph

The sentences are between the entry of the written source graph and other
entries, at the two captures and the original ordered exits. -/

/-- The source graph and the eager spelling are one sentence. -/
private theorem source_eager : RankedValid false (sentenceOf (entryOf source) (entryOf eager.graph)) :=
  (rankedValid_source_iff separable source (expanded join) eager source_expanded).mpr
    (expanded_normal.trans eager_normal.symm)

/-- The source graph and the tree of the expansion of its join are one
sentence. -/
example : RankedValid false (sentenceOf (entryOf source) (entryOf (expanded join).graph)) :=
  (rankedValid_source_iff separable source (expanded join) (expanded join) source_expanded).mpr rfl

/-- The source graph and the graph read back from the joined term are one
sentence. The second graph is not a source graph; it is the checked
realization of the joined LetCase term. -/
example : RankedValid false (sentenceOf (entryOf source)
    (entryOf (CheckedTable.ofLetCase (expanded join).exits_ne_nil (joinedTyping join)))) :=
  (rankedValid_entries_iff separable (entryOf source)
    (entryOf (CheckedTable.ofLetCase (expanded join).exits_ne_nil (joinedTyping join)))
    (expanded join) (expanded join) source_expanded
    ((CheckedTable.ofLetCase_emit false (expanded join).exits_ne_nil (joinedTyping join)).trans
      (joined_native join))).mpr rfl

/-- The source graph and the eager spelling have the same original-entry,
original-exit arrow at the ordered trace model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf source) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_entries_iff separable (entryOf source) (entryOf eager.graph) (expanded join) eager
    source_expanded (CheckedTable.ofLetCase_emit false eager.exits_ne_nil eager.typing)).mpr
    (expanded_normal.trans eager_normal.symm)

/-! ## A changed incoming join value, at the source graph level

The two source graphs differ only in the operand of row 1: the value it
passes to the join. They ask the same requests on every path. -/

/-- The two source graphs are not one sentence. -/
private theorem sources_apart :
    ¬ RankedValid false (sentenceOf (entryOf source) (entryOf sourcePayload)) := fun valid => by
  have same : normalWith 0 0 1 = normalWith 1 1 2 :=
    (expanded_normal.symm.trans ((rankedValid_sources_iff separable source sourcePayload (expanded join)
      (expanded joinPayload) source_expanded sourcePayload_expanded).mp valid)).trans
      expandedPayload_normal
  simp at same

/-- Their original-entry, original-exit arrows differ at the ordered trace
model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf source) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf sourcePayload) :=
  fun same => by
    have terms : normalWith 0 0 1 = normalWith 1 1 2 :=
      (expanded_normal.symm.trans ((denoteRanked_entries_iff separable (entryOf source)
        (entryOf sourcePayload) (expanded join) (expanded joinPayload) source_expanded
        sourcePayload_expanded).mp same)).trans expandedPayload_normal
    simp at terms

/-- The source graph with the changed predecessor is not one sentence with
the eager spelling either. -/
example : ¬ RankedValid false (sentenceOf (entryOf sourcePayload) (entryOf eager.graph)) :=
  fun valid => by
    have same : normalWith 1 1 2 = normalWith 0 0 1 :=
      (expandedPayload_normal.symm.trans ((rankedValid_source_iff separable sourcePayload
        (expanded joinPayload) eager sourcePayload_expanded).mp valid)).trans eager_normal
    simp at same

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
