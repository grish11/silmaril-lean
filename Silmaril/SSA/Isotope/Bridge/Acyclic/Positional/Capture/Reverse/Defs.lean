module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Defs

/-! # The exact captured LetCase grammar and its positional reverse compiler -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {A : τ}

mutual

/-- A block of the emitted LetCase control grammar. Operand derivations are
kept intact. The surrounding grammar supplies the ambient and packet binders. -/
inductive Tree (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d)
    (L : LCtx τ) : τ → Type (max u v) where
  | jump {A B : τ} : Operand Φ (β.snoc A) B → Edge Φ β L B → Tree Φ β L A
  | case {A B D : τ} : Operand Φ (β.snoc A) (coprod B D) →
      Edge Φ β L B → Edge Φ β L D → Tree Φ β L A

/-- An emitted arm either returns the current packet at an exact outward
position or runs another block. -/
inductive Edge (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d)
    (L : LCtx τ) : τ → Type (max u v) where
  | exit {i : Nat} {A : τ} : At L i A → Edge Φ β L A
  | local {A : τ} : Tree Φ β L A → Edge Φ β L A

end

mutual

def Tree.render {A : τ} (t : Tree Φ β L A) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    FiniteExit Φ L (γ.snoc A) :=
  match t with
  | .jump op k => .join (.br (s.operand op)) (k.render (.skip s A))
  | .case op l r => .case (s.operand op) (l.render (.skip s A)) (r.render (.skip s A))
termination_by structural t

def Edge.render {A : τ} (k : Edge Φ β L A) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    FiniteExit Φ L (γ.snoc A) :=
  match k with
  | .exit h => .br h ⟨.bv 0, .bv⟩
  | .local t => t.render s
termination_by structural k

end

/-- The outer binder evaluates the entry operand once and supplies the initial packet. -/
structure Program (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d) (L : LCtx τ) where
  input : τ
  entry : Operand Φ β input
  body : Tree Φ β L input

def Program.toFiniteExit (p : Program Φ β L) : FiniteExit Φ L β :=
  .join (.br p.entry) (p.body.render .base)

def Program.toLetCase (p : Program Φ β L) : Operand Φ β (Region.packedExitType L) :=
  p.toFiniteExit.encode.toLetCase

/-- A typed grammar witness for an actual LetCase term and its original ordered exits. -/
def ResultGrammar (term : Operand Φ β (Region.packedExitType L)) :=
  { p : Program Φ β L // p.toLetCase = term }

variable {k : Nat} {types : Fin k → τ}

abbrev LocalTrees (types : Fin k → τ) (targets : List (Fin k)) :=
  ∀ j, j ∈ targets → Tree Φ β L (types j)

def targetTree (t : Target types L A) {labels : List (Fin k)} (edge : ∀ j ∈ t.locals, j ∈ labels)
    (next : LocalTrees (Φ := Φ) (β := β) (L := L) types labels) : Edge Φ β L A :=
  match t with
  | .local i => .local (next i (edge i (by simp [Target.locals])))
  | .exit h => .exit h

def blockTree (b : Block Φ β types L A) (next : LocalTrees (Φ := Φ) (β := β) (L := L) types b.locals) :
    Tree Φ β L A :=
  match b with
  | .jump op t => .jump op (targetTree t (fun _ h => h) next)
  | .case op l r => .case op
      (targetTree l (fun _ h => List.mem_append_left _ h) next)
      (targetTree r (fun _ h => List.mem_append_right _ h) next)

/-- Read the grammar of the actual forward compiler. Only local edges use
the rank to unfold. No original label numbers are stored in the result. -/
def tableTree {n : Nat} (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1)) :
    Tree Φ β L (p.types i) :=
  blockTree (p.block i) (fun j _ => tableTree p ok j)
termination_by p.rank i
decreasing_by exact p.decreases ok ‹j ∈ _›

def tableProgram {n : Nat} (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : Program Φ β L :=
  ⟨p.types i, a, tableTree p ok i⟩

/-- While numbering the tree, each new block can refer to older blocks and
external exits. Existing local numbers shift together under a new block. -/
inductive Plan (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d)
    (L : LCtx τ) : List τ → Type (max u v) where
  | empty : Plan Φ β L []
  | push {R : List τ} {A : τ} : Plan Φ β L R → Block Φ β R.get L A → Plan Φ β L (A :: R)

variable {R S T : List τ}

def shiftTarget (B : τ) : Target R.get L A → Target (B :: R).get L A
  | .local i => .local i.succ
  | .exit h => .exit h

def shiftBlock (B : τ) : Block Φ β R.get L A → Block Φ β (B :: R).get L A
  | .jump op t => .jump op (shiftTarget B t)
  | .case op l r => .case op (shiftTarget B l) (shiftTarget B r)

/-- The actual block at a positional index after all shifts. -/
def Plan.blockAt : {R : List τ} → Plan Φ β L R → (i : Fin R.length) → Block Φ β R.get L (R.get i)
  | [], .empty, i => i.elim0
  | A :: R, .push p b, i =>
    Fin.cases (motive := fun j => Block Φ β (A :: R).get L ((A :: R).get j))
      (shiftBlock A b) (fun j => shiftBlock A (p.blockAt j)) i

def Plan.toTable (p : Plan Φ β L (A :: R)) : Table Φ β L R.length :=
  ⟨(A :: R).get, p.blockAt⟩

/-- The steps that extend a plan, tracked at the actual source and destination. -/
inductive Extension : {R S : List τ} → Plan Φ β L R → Plan Φ β L S → Type (max u v) where
  | same {R : List τ} (p : Plan Φ β L R) : Extension p p
  | push {R S : List τ} {p : Plan Φ β L R} {q : Plan Φ β L S} {A : τ} :
      Extension p q → (b : Block Φ β S.get L A) → Extension p (q.push b)

def Extension.then {p : Plan Φ β L R} {q : Plan Φ β L S} (h : Extension p q) :
    {T : List τ} → {r : Plan Φ β L T} → Extension q r → Extension p r
  | _, _, .same _ => h
  | _, _, .push prev b => .push (h.then prev) b

def Extension.target {p : Plan Φ β L R} :
    {S : List τ} → {q : Plan Φ β L S} → Extension p q → Target R.get L A → Target S.get L A
  | _, _, .same _, t => t
  | _, _, .push (A := B) next _, t => shiftTarget B (next.target t)

structure BuiltTree (p : Plan Φ β L R) (A : τ) where
  labels : List τ
  tail : Plan Φ β L labels
  extension : Extension p tail
  head : Block Φ β labels.get L A

def BuiltTree.plan {p : Plan Φ β L R} (b : BuiltTree p A) : Plan Φ β L (A :: b.labels) :=
  b.tail.push b.head

structure BuiltEdge (p : Plan Φ β L R) (A : τ) where
  labels : List τ
  plan : Plan Φ β L labels
  extension : Extension p plan
  target : Target labels.get L A

mutual

def Tree.build {A : τ} (t : Tree Φ β L A) {R : List τ} (p : Plan Φ β L R) : BuiltTree p A :=
  match t with
  | .jump op k =>
    let b := k.build p
    ⟨b.labels, b.plan, b.extension, .jump op b.target⟩
  | .case op l r =>
    let b := l.build p
    let c := r.build b.plan
    ⟨c.labels, c.plan, b.extension.then c.extension, .case op (c.extension.target b.target) c.target⟩
termination_by structural t

def Edge.build {A : τ} (k : Edge Φ β L A) {R : List τ} (p : Plan Φ β L R) : BuiltEdge p A :=
  match k with
  | .exit h => ⟨R, p, .same p, .exit h⟩
  | .local t =>
    let b := t.build p
    ⟨A :: b.labels, b.plan, .push b.extension b.head, .local 0⟩
termination_by structural k

end

/-- Number the exact grammar witness from its leaves. The original entry
operand and all outward positions are used directly. -/
def Program.build (p : Program Φ β L) : BuiltTree (Plan.empty : Plan Φ β L []) p.input :=
  p.body.build .empty

def Program.toTable (p : Program Φ β L) : Table Φ β L p.build.labels.length :=
  p.build.plan.toTable

/-- The reverse compiler returns a native entry, the numbered table and a
certificate for the original global rank checker. -/
structure CheckedTable (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d) (L : LCtx τ) where
  size : Nat
  table : Table Φ β L size
  checked : table.check = true
  entry : Operand Φ β (table.types 0)

def CheckedTable.toSSA (c : CheckedTable Φ β L) : Region Φ :=
  c.table.toSSA 0 c.entry

theorem CheckedTable.toSSA_hasType (c : CheckedTable Φ β L) :
    Region.HasType β.toList c.toSSA L :=
  c.table.toSSA_hasType 0 c.entry

def CheckedTable.toLetCase (c : CheckedTable Φ β L) : Operand Φ β (Region.packedExitType L) :=
  c.table.toLetCase c.checked 0 c.entry

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
