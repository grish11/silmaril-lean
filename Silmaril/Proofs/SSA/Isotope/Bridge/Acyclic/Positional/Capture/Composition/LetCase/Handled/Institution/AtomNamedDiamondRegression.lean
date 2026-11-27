module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Source.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs

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
open Silmaril.SSA.LambdaRTL (CFG Val)
open scoped LetSeq.StraightLine.Structural Tagged

set_option backward.isDefEq.respectTransparency false

/-! ## A named block-parameter diamond, through the scoped flat syntax

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

/-! ## The named graph

A named three-address graph with block parameters. A block has one
parameter register, assigned by the jumps to it. Named blocks do not see
the captures of the entry, so every live value is passed in the
parameters.

```
entry:        s = pick later;  br classify (earlier, s)
classify(p):  (w, s) = p;  case test w { a => br reply (a, s) } { b => br payload (b, s) }
reply(p):     (a, s) = p;  e = echo a;  br join (e, s)
payload(p):   br join p
join(p):      (j, s) = p;  f = mark j;  case s { u => br leaf (u, f) } { q => br done (q, j) }
leaf(p):      (u, f) = p;  (x, z) = u;  br done (x, f)
```

`reply` and `payload` are the two predecessors of `join`, and the
parameter of `join` is the phi of the two incoming values. `echo` is the
effect before the join, and `mark` is the request on the joined value
after it. The stored reply `s` of `pick` is inspected in `join`. -/

private inductive Reg | later | earlier | s | p | w | a | b | e | j | f | u | q | x | z
  deriving DecidableEq

private inductive Lbl | classify | reply | payload | join | leaf | done | other
  deriving DecidableEq

/-- The named graph, with the value that `reply` passes to the join. -/
private def named (incoming : Reg) : CFG Reg Lbl Op where
  entry :=
    .let1 .s (.app .pick (.var .later))
      (.term (.br .classify (.pair (.var .earlier) (.var .s))))
  blocks :=
    [(.classify, ⟨.p, .let2 .w .s (.val (.var .p))
        (.term (.case (.app .test (.var .w))
          .a (.br .reply (.pair (.var .a) (.var .s)))
          .b (.br .payload (.pair (.var .b) (.var .s)))))⟩),
     (.reply, ⟨.p, .let2 .a .s (.val (.var .p))
        (.let1 .e (.app .echo (.var .a))
          (.term (.br .join (.pair (.var incoming) (.var .s)))))⟩),
     (.payload, ⟨.p, .term (.br .join (.var .p))⟩),
     (.join, ⟨.p, .let2 .j .s (.val (.var .p))
        (.let1 .f (.app .mark (.var .j))
          (.term (.case (.val (.var .s))
            .u (.br .leaf (.pair (.var .u) (.var .f)))
            .q (.br .done (.pair (.var .q) (.var .j))))))⟩),
     (.leaf, ⟨.p, .let2 .u .f (.val (.var .p))
        (.let2 .x .z (.val (.var .u))
          (.term (.br .done (.pair (.var .x) (.var .f)))))⟩)]

private abbrev captures : Fin 2 → Reg := ![.later, .earlier]

/-- The named graph elaborates to a scoped flat graph. -/
private theorem named_elaborates (incoming : Reg) (h : incoming = .e ∨ incoming = .a) :
    (Bridge.NamedFlat.elaborate (named incoming) [.done, .other] captures).isSome = true := by
  rcases h with rfl | rfl <;> decide +kernel

/-- The scoped flat graph of the named graph: five blocks, two exits and
two captures. It is the output of the existing elaboration. -/
private def flat : FiniteCFG Op 5 2 2 :=
  (Bridge.NamedFlat.elaborate (named .e) [.done, .other] captures).get (named_elaborates .e (.inl rfl))

/-- The flat graph of the named graph in which `reply` passes its own
payload `a` to the join. -/
private def flatPayload : FiniteCFG Op 5 2 2 :=
  (Bridge.NamedFlat.elaborate (named .a) [.done, .other] captures).get (named_elaborates .a (.inr rfl))

/-! ## The typed witness and the table

The existing typed witness of a flat graph gives each literal operand its
typing. The parameters of the five blocks are a pair of an atom and the
stored reply, except for `leaf`, whose parameter is a pair of a pair of
atoms and an atom. -/

private abbrev packet : Ty Unit := .product tok sumTy
private abbrev leafPacket : Ty Unit := .product pairTy tok
private abbrev rowTypes : Fin 5 → Ty Unit := ![packet, packet, packet, packet, leafPacket]
private abbrev exitTypes : Fin 2 → Ty Unit := ![pairTy, tok]
private abbrev labelTypes : Fin (5 + 2) → Ty Unit := SSA.FiniteSum.append rowTypes exitTypes

/-- The contexts of the blocks: under the parameter, after the parameter
is destructured, and after one more binding; and the same for `leaf`. -/
private abbrev inPacket : BoundCtx (Ty Unit) 3 := older.snoc packet
private abbrev opened : BoundCtx (Ty Unit) 5 := (inPacket.snoc tok).snoc sumTy
private abbrev bound : BoundCtx (Ty Unit) 6 := opened.snoc tok
private abbrev inLeaf : BoundCtx (Ty Unit) 3 := older.snoc leafPacket
private abbrev leafOpened : BoundCtx (Ty Unit) 5 := (inLeaf.snoc pairTy).snoc tok
private abbrev leafLeaf : BoundCtx (Ty Unit) 7 := (leafOpened.snoc tok).snoc tok

/-- The literal operands of the flat graph, with their typings: the
request of the entry and the packet it passes on; a parameter; the
requests of the blocks; the packets passed on a jump; the stored reply;
and the operands of `leaf`. -/
private def opPick : Operand Op older sumTy := ⟨.op Op.pick (.bv 0), .op .bv⟩
private def opEntryArg : Operand Op (older.snoc sumTy) packet := ⟨.pair (.bv 2) (.bv 0), .pair .bv .bv⟩
private def opPacket : Operand Op inPacket packet := ⟨.bv 0, .bv⟩
private def opTest : Operand Op opened testTy := ⟨.op Op.test (.bv 1), .op .bv⟩
private def opEcho : Operand Op opened tok := ⟨.op Op.echo (.bv 1), .op .bv⟩
private def opMark : Operand Op opened tok := ⟨.op Op.mark (.bv 1), .op .bv⟩
private def opArm : Operand Op bound packet := ⟨.pair (.bv 0) (.bv 1), .pair .bv .bv⟩
private def opOwn : Operand Op bound packet := ⟨.pair (.bv 2) (.bv 1), .pair .bv .bv⟩
private def opStored : Operand Op bound sumTy := ⟨.bv 1, .bv⟩
private def opLeafArg : Operand Op (bound.snoc pairTy) leafPacket := ⟨.pair (.bv 0) (.bv 1), .pair .bv .bv⟩
private def opDoneArg : Operand Op (bound.snoc tok) pairTy := ⟨.pair (.bv 0) (.bv 3), .pair .bv .bv⟩
private def opLeafPacket : Operand Op inLeaf leafPacket := ⟨.bv 0, .bv⟩
private def opInner : Operand Op leafOpened pairTy := ⟨.bv 1, .bv⟩
private def opResult : Operand Op leafLeaf pairTy := ⟨.pair (.bv 1) (.bv 2), .pair .bv .bv⟩

/-- The typed witness of `classify`. -/
private def bodyClassify :
    FlatLetCase.Body Op labelTypes inPacket (flat.block 0) :=
  .let₂ opPacket (.case opTest (FlatLetCase.Body.br (L := labelTypes) (1 : Fin 7) opArm) (FlatLetCase.Body.br (L := labelTypes) (2 : Fin 7) opArm))

/-- The typed witness of `reply`. -/
private def bodyReply :
    FlatLetCase.Body Op labelTypes inPacket (flat.block 1) :=
  .let₂ opPacket (.let₁ opEcho (FlatLetCase.Body.br (L := labelTypes) (3 : Fin 7) opArm))

/-- The typed witness of `payload`. -/
private def bodyPayload :
    FlatLetCase.Body Op labelTypes inPacket (flat.block 2) :=
  FlatLetCase.Body.br (L := labelTypes) (3 : Fin 7) opPacket

/-- The typed witness of `join`. -/
private def bodyJoin :
    FlatLetCase.Body Op labelTypes inPacket (flat.block 3) :=
  .let₂ opPacket (.let₁ opMark (.case opStored (FlatLetCase.Body.br (L := labelTypes) (4 : Fin 7) opLeafArg) (FlatLetCase.Body.br (L := labelTypes) (5 : Fin 7) opDoneArg)))

/-- The typed witness of `leaf`. -/
private def bodyLeaf :
    FlatLetCase.Body Op labelTypes inLeaf (flat.block 4) :=
  .let₂ opLeafPacket (.let₂ opInner (FlatLetCase.Body.br (L := labelTypes) (5 : Fin 7) opResult))

/-- The typed witness of the flat graph. -/
private def witness : FlatLetCase.Witness flat older rowTypes exitTypes where
  entry := .let₁ opPick (FlatLetCase.Body.br (L := labelTypes) (0 : Fin 7) opEntryArg)
  block := fun i =>
    (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j)) (flat.block j))
        bodyClassify
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ)) (flat.block j.succ))
        bodyReply
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ)) (flat.block j.succ.succ))
        bodyPayload
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ.succ)) (flat.block j.succ.succ.succ))
        bodyJoin
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ.succ.succ)) (flat.block j.succ.succ.succ.succ))
        bodyLeaf
        (fun j => j.elim0) j) j) j) j) j) i

/-- Every block is a row and the entry is a line to `classify`. -/
private theorem delimited : witness.Delimited := ⟨by decide +kernel, by decide +kernel⟩

/-- The rank check of the flat graph gives the check of the table. -/
private theorem checked : (witness.table delimited).check = true :=
  FlatLetCase.Witness.table_check witness delimited (by decide +kernel)

/-- The checked table of the flat graph: its entry, its five rows in
order, and its two ordered exits. -/
private def source : CheckedTable Op older exits :=
  witness.checkedTable delimited checked

/-- The typed witness of `classify`. -/
private def bodyClassifyPayload :
    FlatLetCase.Body Op labelTypes inPacket (flatPayload.block 0) :=
  .let₂ opPacket (.case opTest (FlatLetCase.Body.br (L := labelTypes) (1 : Fin 7) opArm) (FlatLetCase.Body.br (L := labelTypes) (2 : Fin 7) opArm))

/-- The typed witness of `reply`. -/
private def bodyReplyPayload :
    FlatLetCase.Body Op labelTypes inPacket (flatPayload.block 1) :=
  .let₂ opPacket (.let₁ opEcho (FlatLetCase.Body.br (L := labelTypes) (3 : Fin 7) opOwn))

/-- The typed witness of `payload`. -/
private def bodyPayloadPayload :
    FlatLetCase.Body Op labelTypes inPacket (flatPayload.block 2) :=
  FlatLetCase.Body.br (L := labelTypes) (3 : Fin 7) opPacket

/-- The typed witness of `join`. -/
private def bodyJoinPayload :
    FlatLetCase.Body Op labelTypes inPacket (flatPayload.block 3) :=
  .let₂ opPacket (.let₁ opMark (.case opStored (FlatLetCase.Body.br (L := labelTypes) (4 : Fin 7) opLeafArg) (FlatLetCase.Body.br (L := labelTypes) (5 : Fin 7) opDoneArg)))

/-- The typed witness of `leaf`. -/
private def bodyLeafPayload :
    FlatLetCase.Body Op labelTypes inLeaf (flatPayload.block 4) :=
  .let₂ opLeafPacket (.let₂ opInner (FlatLetCase.Body.br (L := labelTypes) (5 : Fin 7) opResult))

/-- The typed witness of the flat graph in which `reply` passes its payload. -/
private def witnessPayload : FlatLetCase.Witness flatPayload older rowTypes exitTypes where
  entry := .let₁ opPick (FlatLetCase.Body.br (L := labelTypes) (0 : Fin 7) opEntryArg)
  block := fun i =>
    (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j)) (flatPayload.block j))
        bodyClassifyPayload
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ)) (flatPayload.block j.succ))
        bodyReplyPayload
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ)) (flatPayload.block j.succ.succ))
        bodyPayloadPayload
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ.succ)) (flatPayload.block j.succ.succ.succ))
        bodyJoinPayload
        (fun j => Fin.cases (motive := fun j => FlatLetCase.Body Op labelTypes
          (older.snoc (rowTypes j.succ.succ.succ.succ)) (flatPayload.block j.succ.succ.succ.succ))
        bodyLeafPayload
        (fun j => j.elim0) j) j) j) j) j) i

/-- Every block is a row and the entry is a line to `classify`. -/
private theorem delimitedPayload : witnessPayload.Delimited := ⟨by decide +kernel, by decide +kernel⟩

/-- The rank check of the flat graph gives the check of the table. -/
private theorem checkedPayload : (witnessPayload.table delimitedPayload).check = true :=
  FlatLetCase.Witness.table_check witnessPayload delimitedPayload (by decide +kernel)

/-- The checked table of the flat graph: its entry, its five rows in
order, and its two ordered exits. -/
private def sourcePayload : CheckedTable Op older exits :=
  witnessPayload.checkedTable delimitedPayload checkedPayload

/-! ## The checked readback of the table

The rows of the table are the folded blocks. The readback unfolds them
from the entry; `join` and `leaf` are unfolded once under each
predecessor. -/

/-- The folded operands of the rows that do not depend on the incoming
value. -/
private def classifyRow : Operand Op (older.snoc packet) (.coprod packet packet) :=
  ⟨.let₂ (.bv 0) (.case (.op .test (.bv 1)) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 1)))),
    .let₂ .bv (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))⟩

private def payloadRow : Operand Op (older.snoc packet) packet := ⟨.bv 0, .bv⟩

private def joinRow : Operand Op (older.snoc packet) (.coprod leafPacket pairTy) :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .mark (.bv 1))
      (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))),
    .let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))⟩

private def leafRow : Operand Op (older.snoc leafPacket) pairTy :=
  ⟨.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2))), .let₂ .bv (.let₂ .bv (.pair .bv .bv))⟩

/-- The folded operand of `reply`. -/
private def replyRow : Operand Op (older.snoc packet) packet :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .echo (.bv 1)) (.pair (.bv 0) (.bv 1))),
    .let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))⟩

private theorem compile_classify {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witness.table delimited).compileAt checked 0 s =
      .case (s.operand classifyRow) ((witness.table delimited).compileAt checked 1 (.skip s packet))
        ((witness.table delimited).compileAt checked 2 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_reply {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witness.table delimited).compileAt checked 1 s =
      .join (.br (s.operand replyRow)) ((witness.table delimited).compileAt checked 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_payload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witness.table delimited).compileAt checked 2 s =
      .join (.br (s.operand payloadRow)) ((witness.table delimited).compileAt checked 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_join {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witness.table delimited).compileAt checked 3 s =
      .case (s.operand joinRow) ((witness.table delimited).compileAt checked 4 (.skip s packet))
        (.br (i := 0) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_leaf {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witness.table delimited).compileAt checked 4 s =
      .join (.br (s.operand leafRow)) (.br (i := 0) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

/-- The term read back from the table. -/
private abbrev readbackTerm : Term 2 :=
  (.let₁ (.let₁ (.op Op.pick (.bv 0)) (.pair (.bv 2) (.bv 0)))
    (.case (.let₂ (.bv 0) (.case (.op Op.test (.bv 1)) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 1)))))
      (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 0) (.bv 1))))
        (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
          (.inl (.bv 0))))
      (.let₁ (.bv 0)
        (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
          (.inl (.bv 0))))))

private theorem source_readback : source.toLetCase.1 = readbackTerm := by
  show ((witness.table delimited).toLetCase checked 0 (witness.entryOperand.get delimited.entry)).1 = readbackTerm
  unfold Table.toLetCase Table.toFiniteExit
  rw [compile_classify .base, compile_reply (.skip .base packet),
    compile_payload (.skip .base packet), compile_join (.skip (.skip .base packet) packet),
    compile_leaf (.skip (.skip (.skip .base packet) packet) packet)]
  decide +kernel

/-- The folded operand of `reply`. -/
private def replyRowPayload : Operand Op (older.snoc packet) packet :=
  ⟨.let₂ (.bv 0) (.let₁ (.op .echo (.bv 1)) (.pair (.bv 2) (.bv 1))),
    .let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))⟩

private theorem compile_classifyPayload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witnessPayload.table delimitedPayload).compileAt checkedPayload 0 s =
      .case (s.operand classifyRow) ((witnessPayload.table delimitedPayload).compileAt checkedPayload 1 (.skip s packet))
        ((witnessPayload.table delimitedPayload).compileAt checkedPayload 2 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_replyPayload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witnessPayload.table delimitedPayload).compileAt checkedPayload 1 s =
      .join (.br (s.operand replyRowPayload)) ((witnessPayload.table delimitedPayload).compileAt checkedPayload 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_payloadPayload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witnessPayload.table delimitedPayload).compileAt checkedPayload 2 s =
      .join (.br (s.operand payloadRow)) ((witnessPayload.table delimitedPayload).compileAt checkedPayload 3 (.skip s packet)) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_joinPayload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witnessPayload.table delimitedPayload).compileAt checkedPayload 3 s =
      .case (s.operand joinRow) ((witnessPayload.table delimitedPayload).compileAt checkedPayload 4 (.skip s packet))
        (.br (i := 0) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

private theorem compile_leafPayload {m : Nat} {γ : BoundCtx (Ty Unit) m} (s : Scope older γ) :
    (witnessPayload.table delimitedPayload).compileAt checkedPayload 4 s =
      .join (.br (s.operand leafRow)) (.br (i := 0) rfl ⟨.bv 0, .bv⟩) := by
  rw [Table.compileAt.eq_def]
  rfl

/-- The term read back from the table. -/
private abbrev readbackPayloadTerm : Term 2 :=
  (.let₁ (.let₁ (.op Op.pick (.bv 0)) (.pair (.bv 2) (.bv 0)))
    (.case (.let₂ (.bv 0) (.case (.op Op.test (.bv 1)) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 1)))))
      (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 2) (.bv 1))))
        (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
          (.inl (.bv 0))))
      (.let₁ (.bv 0)
        (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
          (.inl (.bv 0))))))

private theorem sourcePayload_readback : sourcePayload.toLetCase.1 = readbackPayloadTerm := by
  show ((witnessPayload.table delimitedPayload).toLetCase checkedPayload 0 (witnessPayload.entryOperand.get delimitedPayload.entry)).1 = readbackPayloadTerm
  unfold Table.toLetCase Table.toFiniteExit
  rw [compile_classifyPayload .base, compile_replyPayload (.skip .base packet),
    compile_payloadPayload (.skip .base packet), compile_joinPayload (.skip (.skip .base packet) packet),
    compile_leafPayload (.skip (.skip (.skip .base packet) packet) packet)]
  decide +kernel

/-! ## The readback is natively a tree

The packets are removed by native laws, as for the table written by hand:
the sequencing laws, case beta at an injection, pure-let beta, and the
derived equation for a pattern let on a pair of slots. -/

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
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.case (.let₂
      .bv (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff
      := false) (.pair .bv .bv) (.pair .bv .bv) (.case (.let₂ .bv (.case (.op .bv) (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₂
      (.pair .bv .bv) (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂
      .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁
      (let_pair_slots (2 : Fin 3) (0 : Fin 3) rfl rfl (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv)))) (.refl (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv)))
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase (.op
      .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op
      .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.let₁ (A := .coprod packet
      packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv)))
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.case (.inl (.pair (.bv 0) (.bv 1)))
            (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 0) (.bv 1))))
              (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                (.inl (.bv 0))))
            (.let₁ (.bv 0)
              (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                (.inl (.bv 0)))))
          (.let₁ (.inr (.pair (.bv 0) (.bv 1)))
            (.case (.bv 0)
              (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 0) (.bv 1))))
                (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))
              (.let₁ (.bv 0)
                (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.caseBetaL (B := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair
      .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁
      .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (.refl
      (.let₁ (A := .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))) (.refl (.let₁ (A := .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (A := .coprod packet
      packet) (pureEff := false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.caseBetaR (A := packet)
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂
      .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁ (.op .bv) (.pair .bv
      .bv))) (.refl (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))
      (.refl (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.let₁ (.op Op.echo (.bv 0)) (.pair (.bv 0) (.bv 2)))
            (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))
          (.let₁ (.pair (.bv 0) (.bv 1))
            (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair
      .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (.refl
      (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₂ (.pair .bv .bv) (.let₁ (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op
      .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (let_pair_slots (0 : Fin 5) (2 : Fin 5) rfl
      rfl (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.refl (.case
      .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.let₁ (.case (.bv 3) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 2))))
                (.case (.bv 0)
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))
          (.case (.let₂ (.pair (.bv 0) (.bv 1)) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
            (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
            (.inl (.bv 0)))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.caseBetaL (B := pairTy) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl
      (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv
      .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))
      (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.let₁ (let_pair_slots (0 : Fin 7) (1 : Fin 7) rfl rfl (.let₂ .bv (.pair .bv .bv)))
      (.refl (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl
      (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket
      pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl
      .bv)) (.inl .bv))))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (.bv 3)) (.inl (.bv 0))))
                (.let₁ (.inr (.pair (.bv 0) (.bv 2)))
                  (.case (.bv 0)
                    (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2))))
                      (.inl (.bv 0)))
                    (.inl (.bv 0)))))))
          (.case (.let₂ (.pair (.bv 0) (.bv 1)) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
            (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
            (.inl (.bv 0)))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (A := .coprod leafPacket pairTy)
      (pureEff := false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) (.refl (.case (.let₂ (.pair .bv .bv)
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.caseBetaR (A := leafPacket) (.pair .bv .bv)
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case (.let₂
      (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv)
      (.pair .bv .bv) (.inl .bv))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.bindCase (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv)))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.refl (.case .bv (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 2))))))
          (.let₁ (.let₁ (.op Op.mark (.bv 0)) (.case (.bv 2) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 2)))))
            (.case (.bv 0)
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.bindLet (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.caseBetaL (B := pairTy) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv
      .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (Equiv.let₁
      (let_pair_slots (0 : Fin 6) (1 : Fin 6) rfl rfl (.let₂ .bv (.pair .bv .bv))) (.refl (.inl
      .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 2))))))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 2)
              (.let₁ (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.inl (.bv 0)))
              (.let₁ (.inr (.pair (.bv 0) (.bv 2)))
                (.case (.bv 0)
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket
      pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl
      .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (Equiv.let₂
      (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.inl .bv)))
      (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff :=
      false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.caseBetaR (A := leafPacket) (.pair .bv .bv) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.op .bv)
      (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair
      .bv .bv))))) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv
      .bv)))))) ?_
  show Equiv false Γ₀ older
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
      expandedTerm (packedExitType exits)
  exact .refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₁ (.op .bv) (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv))))) (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))))

/-- The same term when `reply` passes its payload: `mark` takes the
payload, and the second tag of `s` returns it. -/
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
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.case (.let₂
      .bv (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff
      := false) (.pair .bv .bv) (.pair .bv .bv) (.case (.let₂ .bv (.case (.op .bv) (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₂
      (.pair .bv .bv) (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))) (.let₁ (.let₂
      .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁
      (let_pair_slots (2 : Fin 3) (0 : Fin 3) rfl rfl (.case (.op .bv) (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv)))) (.refl (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv)))
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase (.op
      .bv) (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op
      .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.letBeta (A := .coprod packet packet) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.let₁ (A := .coprod packet
      packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv)))
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.case (.inl (.pair (.bv 0) (.bv 1)))
            (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 2) (.bv 1))))
              (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                (.inl (.bv 0))))
            (.let₁ (.bv 0)
              (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                (.inl (.bv 0)))))
          (.let₁ (.inr (.pair (.bv 0) (.bv 1)))
            (.case (.bv 0)
              (.let₁ (.let₂ (.bv 0) (.let₁ (.op Op.echo (.bv 1)) (.pair (.bv 2) (.bv 1))))
                (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))
              (.let₁ (.bv 0)
                (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.caseBetaL (B := packet) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair
      .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁
      .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (.refl
      (.let₁ (A := .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₁
      (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv
      (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))) (.refl (.let₁ (A := .coprod packet packet) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (A := .coprod packet
      packet) (pureEff := false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.caseBetaR (A := packet)
      (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂ .bv (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂
      .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.pair .bv .bv))) (.case (.let₂
      .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (pureEff := false)
      (.pair .bv .bv) (.pair .bv .bv) (.let₁ .bv (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁ (.op .bv) (.pair .bv
      .bv))) (.refl (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))
      (.refl (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv
      .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.let₁ (.op Op.echo (.bv 0)) (.pair (.bv 1) (.bv 2)))
            (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))
          (.let₁ (.pair (.bv 0) (.bv 1))
            (.case (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.bindLet (.op .bv) (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))) (.refl (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair
      .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))) (.refl
      (.let₁ (.pair .bv .bv) (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.case (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.let₂ (.pair .bv .bv) (.let₁ (.op .bv)
      (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op
      .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (let_pair_slots (1 : Fin 5) (2 : Fin 5) rfl
      rfl (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.refl (.case
      .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLet (.op .bv) (.case .bv (.inl (.pair .bv .bv))
      (.inr (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv)))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 1))
              (.let₁ (.case (.bv 3) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))
                (.case (.bv 0)
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))
          (.case (.let₂ (.pair (.bv 0) (.bv 1)) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
            (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
            (.inl (.bv 0)))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.caseBetaL (B := pairTy) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl
      (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv
      .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))
      (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.let₁ (let_pair_slots (0 : Fin 7) (1 : Fin 7) rfl rfl (.let₂ .bv (.pair .bv .bv)))
      (.refl (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl
      (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair
      .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket
      pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl
      .bv)) (.inl .bv))))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl
      (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 1))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.let₁ (.pair (.bv 1) (.bv 3)) (.inl (.bv 0))))
                (.let₁ (.inr (.pair (.bv 0) (.bv 3)))
                  (.case (.bv 0)
                    (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2))))
                      (.inl (.bv 0)))
                    (.inl (.bv 0)))))))
          (.case (.let₂ (.pair (.bv 0) (.bv 1)) (.let₁ (.op Op.mark (.bv 1)) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 3))))))
            (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
            (.inl (.bv 0)))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.let₂ (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) (.refl (.case
      (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv
      .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (A := .coprod leafPacket pairTy)
      (pureEff := false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) (.refl (.case (.let₂ (.pair .bv .bv)
      (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv
      (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.caseBetaR (A := leafPacket) (.pair .bv .bv)
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) (.refl (.case (.let₂
      (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))))
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (.refl (.let₂ .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv)
      (.pair .bv .bv) (.inl .bv))))) (.refl (.case (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case
      .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.bindCase (.let₂ (.pair .bv .bv) (.let₁ (.op .bv) (.case .bv
      (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv
      .bv))) (.inl .bv)) (.inl .bv)))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁
      (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv))))) (.refl (.case .bv (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 1))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.let₁ (.op Op.mark (.bv 0)) (.case (.bv 2) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 2)))))
            (.case (.bv 0)
              (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
              (.inl (.bv 0))))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.bindLet (.op .bv) (.case .bv (.inl (.pair .bv .bv)) (.inr
      (.pair .bv .bv))) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl
      .bv))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindLetCase .bv (.inl (.pair
      .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff := false) (.inl (.pair .bv .bv))
      (.inl (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv))
      (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv
      (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.caseBetaL (B := pairTy) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv)))
      (.inl .bv)) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv))
      (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv
      .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))))
      ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (Equiv.let₁
      (let_pair_slots (0 : Fin 6) (1 : Fin 6) rfl rfl (.let₂ .bv (.pair .bv .bv))) (.refl (.inl
      .bv))) (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁
      (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 1))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 3))))))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 2)
              (.let₁ (.let₂ (.bv 0) (.pair (.bv 1) (.bv 3))) (.inl (.bv 0)))
              (.let₁ (.inr (.pair (.bv 0) (.bv 2)))
                (.case (.bv 0)
                  (.let₁ (.let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.bv 2)))) (.inl (.bv 0)))
                  (.inl (.bv 0))))))))
      expandedPayloadTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.bindLetPair .bv (.pair .bv .bv) (.inl .bv)) (.refl (.let₁ (A := .coprod leafPacket
      pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv (.pair .bv .bv))) (.inl
      .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (Equiv.let₂
      (.refl .bv) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.inl .bv)))
      (.refl (.let₁ (A := .coprod leafPacket pairTy) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (A := .coprod leafPacket pairTy) (pureEff :=
      false) (.inr (.pair .bv .bv)) (.inr (.pair .bv .bv)) (.case .bv (.let₁ (.let₂ .bv (.let₂ .bv
      (.pair .bv .bv))) (.inl .bv)) (.inl .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.caseBetaR (A := leafPacket) (.pair .bv .bv) (.let₁ (.let₂
      .bv (.let₂ .bv (.pair .bv .bv))) (.inl .bv)) (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv) (.refl (.let₂
      .bv (.inl (.pair .bv .bv)))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.inl .bv)))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.op .bv)
      (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair
      .bv .bv))))) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv
      .bv)))))) ?_
  show Equiv false Γ₀ older
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
      expandedPayloadTerm (packedExitType exits)
  exact .refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₁ (.op .bv) (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv))))) (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))))

/-! ## The flat graph and its table

The translation keeps the control structure of the flat graph: the entry
jumps to `classify`, every row jumps to the labels of its block, and the
local targets and the rank check are those of the flat graph. -/

/-- The blocks of the flat graph that `reply` and `payload` jump to: both
jump to `join`, the fourth block. -/
example : (List.finRange 5).map (FlatLetCase.localTargets flat) = [[1, 2], [3], [3], [4], []] := by
  decide +kernel

/-- The table has the same local targets, row by row. -/
example (i : Fin 5) : (witness.table delimited).localTargets i = FlatLetCase.localTargets flat i :=
  FlatLetCase.Witness.table_localTargets witness delimited i

/-- Every row of the table jumps to the labels of its block: `join` to
`leaf` and to the first exit, `leaf` to the first exit. -/
example : (List.finRange 5).map (fun i => FlatLetCase.jumps (flat.block i)) =
    [[1, 2], [3], [3], [4, 5], [5]] := by decide +kernel

example (i : Fin 5) :
    FlatLetCase.jumps (((witness.table delimited).block i).toFlat List.length_ofFn) =
      FlatLetCase.jumps (flat.block i) :=
  FlatLetCase.Witness.table_jumps witness delimited i

/-- The entry of the flat graph jumps to `classify`, the entry row of the
table. -/
example : FlatLetCase.jumps flat.entry = [0] := FlatLetCase.Witness.entry_jumps witness delimited

/-! ## The join node and its expansion

The program of the named graph as a join: under the stored reply, the reply of `test` is
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

/-- The join node of the named graph. -/
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

/-- The join node of the named graph in which `reply` passes its payload. -/
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

/-! ## The readback the flat graph already has

The existing flat readback unfolds the witnessed flat graph itself, with
its lets in place. It is natively equal to the same tree, so it is
natively equal to the checked readback of the table: on this graph the
translation keeps the readback. -/

private theorem flatRanked : Rank.check (FlatLetCase.localTargets flat) = true := by decide +kernel

/-- The term of the existing flat readback of the flat graph. -/
private abbrev flatReadbackTerm : Term 2 :=
  (.let₁ (.op Op.pick (.bv 0))
    (.let₁ (.pair (.bv 2) (.bv 0))
      (.let₂ (.bv 0)
        (.case (.op Op.test (.bv 1))
          (.let₁ (.pair (.bv 0) (.bv 1))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 1))
                (.let₁ (.pair (.bv 0) (.bv 1))
                  (.let₂ (.bv 0)
                    (.let₁ (.op Op.mark (.bv 1))
                      (.case (.bv 1)
                        (.let₁ (.pair (.bv 0) (.bv 1))
                          (.let₂ (.bv 0) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))))
                        (.inl (.pair (.bv 0) (.bv 3))))))))))
          (.let₁ (.pair (.bv 0) (.bv 1))
            (.let₁ (.bv 0)
              (.let₂ (.bv 0)
                (.let₁ (.op Op.mark (.bv 1))
                  (.case (.bv 1)
                    (.let₁ (.pair (.bv 0) (.bv 1))
                      (.let₂ (.bv 0) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))))
                    (.inl (.pair (.bv 0) (.bv 3))))))))))))

private theorem flat_readback :
    (FlatLetCase.compile witness flatRanked).toLetCase.1 = flatReadbackTerm := by decide +kernel

private theorem flatReadback_expanded :
    Equiv false Γ₀ older flatReadbackTerm expandedTerm (packedExitType exits) := by
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff
      := false) (.pair .bv .bv) (.pair .bv .bv) (.let₂ .bv (.case (.op .bv) (.let₁ (.pair .bv .bv)
      (.let₂ .bv (.let₁ (.op .bv) (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₁ (.op .bv) (.case .bv
      (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair .bv
      .bv))))))))) (.let₁ (.pair .bv .bv) (.let₁ .bv (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁
      (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair .bv
      .bv))))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (let_pair_slots (2 : Fin
      3) (0 : Fin 3) rfl rfl (.case (.op .bv) (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₁ (.op .bv)
      (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂
      .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv))))))))) (.let₁ (.pair .bv .bv)
      (.let₁ .bv (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv
      (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₂ .bv (.let₁ (.op
      .bv) (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv)
      (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv))))))))) (.refl (.let₁
      (.pair .bv .bv) (.let₁ .bv (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv)
      (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁ (.op .bv) (.let₁ (.pair .bv .bv)
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ .bv
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair
      .bv .bv) (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv
      (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv))))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ .bv
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (let_pair_slots (0 : Fin 5) (2 : Fin 5) rfl rfl (.let₁
      (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv)))))
      (.inl (.pair .bv .bv)))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ .bv (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl
      (.pair .bv .bv)))))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 3)
                (.let₁ (.pair (.bv 0) (.bv 1))
                  (.let₂ (.bv 0) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))))
                (.inl (.pair (.bv 0) (.bv 2))))))
          (.let₁ (.pair (.bv 0) (.bv 1))
            (.let₁ (.bv 0)
              (.let₂ (.bv 0)
                (.let₁ (.op Op.mark (.bv 1))
                  (.case (.bv 1)
                    (.let₁ (.pair (.bv 0) (.bv 1))
                      (.let₂ (.bv 0) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))))
                    (.inl (.pair (.bv 0) (.bv 3))))))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.refl (.inl (.pair .bv .bv)))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ .bv
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (let_pair_slots (0 : Fin 7) (1 : Fin 7) rfl rfl (.let₂ .bv (.inl (.pair .bv .bv)))) (.refl
      (.inl (.pair .bv .bv)))))) (.refl (.let₁ (.pair .bv .bv) (.let₁ .bv (.let₂ .bv (.let₁ (.op
      .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl
      (.pair .bv .bv)))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.let₁ .bv (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv
      (.inl (.pair .bv .bv))))) (.inl (.pair .bv .bv))))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv)
      (.let₂ .bv (.let₁ (.op .bv) (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.inl (.pair .bv .bv)))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (let_pair_slots (0 : Fin 4) (1 : Fin 4) rfl rfl (.let₁ (.op .bv)
      (.case .bv (.let₁ (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl (.pair .bv .bv))))) (.inl (.pair
      .bv .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (Equiv.letBeta (pureEff := false) (.pair .bv .bv) (.pair .bv .bv) (.let₂ .bv (.let₂ .bv (.inl
      (.pair .bv .bv))))) (.refl (.inl (.pair .bv .bv))))))) ?_
  show Equiv false Γ₀ older
      (.let₁ (.op Op.pick (.bv 0))
        (.case (.op Op.test (.bv 2))
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 3)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 2))))))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 2)
              (.let₂ (.pair (.bv 0) (.bv 1)) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2)))))
              (.inl (.pair (.bv 0) (.bv 2)))))))
      expandedTerm (packedExitType exits)
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl (.op
      .bv)) (.refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv)))
      (.inl (.pair .bv .bv)))))) (Equiv.let₁ (.refl (.op .bv)) (Equiv.case (.refl .bv)
      (let_pair_slots (0 : Fin 6) (1 : Fin 6) rfl rfl (.let₂ .bv (.inl (.pair .bv .bv)))) (.refl
      (.inl (.pair .bv .bv))))))) ?_
  refine LetCase.LocallyNameless.Equiv.trans (Equiv.let₁ (.refl (.op .bv)) (Equiv.bindCase (.op .bv)
      (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair
      .bv .bv))))) (.let₁ (.op .bv) (.case .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv
      .bv)))))) ?_
  exact .refl (.let₁ (.op .bv) (.let₁ (.op .bv) (.case .bv (.let₁ (.op .bv) (.let₁ (.op .bv) (.case
      .bv (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv))))) (.let₁ (.op .bv) (.case .bv
      (.let₂ .bv (.inl (.pair .bv .bv))) (.inl (.pair .bv .bv)))))))

/-- The existing readback of the flat graph and the checked readback of
its table are natively equal. -/
example : Equiv false Γ₀ older (FlatLetCase.compile witness flatRanked).toLetCase.1 source.toLetCase.1
    (packedExitType exits) :=
  flat_readback ▸ source_readback ▸ flatReadback_expanded.trans readback_expanded.symm

/-! ## The named graph, the join and the expansion -/

/-- The readback of the table of the named graph is natively equal to the
expansion of the join. -/
private theorem source_expanded :
    Equiv false Γ₀ older source.toLetCase.1 (around join.expand.term) (packedExitType exits) :=
  source_readback ▸ expanded_term ▸ readback_expanded

private theorem sourcePayload_expanded :
    Equiv false Γ₀ older sourcePayload.toLetCase.1 (around joinPayload.expand.term)
      (packedExitType exits) :=
  sourcePayload_readback ▸ expandedPayload_term ▸ readbackPayload_expanded

/-- The readback of the table of the named graph is natively equal to the
joined term, with the continuation written once. -/
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

/-- The readback of the table of the named graph is natively equal to the
normal form of the join. -/
example : Equiv false Γ₀ older source.toLetCase.1 (normalWith 0 0 1) (packedExitType exits) :=
  source_expanded.trans (expanded_normal ▸ spelled_equiv_normal (expanded join))

/-! ## Ranked validity and ordered-exit arrows

The sentences are between the entry of the table of the named graph and
other entries, at the two captures and the original ordered exits. -/

/-- The table of the named graph and the tree of the expansion of its join
are one sentence. -/
example : RankedValid false (sentenceOf (entryOf source) (entryOf (expanded join).graph)) :=
  (rankedValid_source_iff separable source (expanded join) (expanded join) source_expanded).mpr rfl

/-- They have the same original-entry, original-exit arrow at the ordered
trace model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf source) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf (expanded join).graph) :=
  (denoteRanked_entries_iff separable (entryOf source) (entryOf (expanded join).graph) (expanded join)
    (expanded join) source_expanded
    (CheckedTable.ofLetCase_emit false (expanded join).exits_ne_nil (expanded join).typing)).mpr rfl

/-! ## A changed incoming join value, at the named graph level

The two named graphs differ only in the value that `reply` passes to
`join`. They ask the same requests on every path. -/

/-- The tables of the two named graphs are not one sentence. -/
private theorem named_apart :
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

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
