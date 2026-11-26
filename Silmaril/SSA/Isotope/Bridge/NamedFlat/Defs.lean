module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs

/-! # Elaborating a named cyclic table into scoped Isotope blocks -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LetCase.LocallyNameless (Tm)

universe v w
variable {V K : Type w} {F : Type v} {n labels : Nat}

/-- A partial binding map into the newest-first positional context. -/
abbrev Names (V : Type w) (n : Nat) := V → Option (Fin n)

def bindName [DecidableEq V] (names : Names V n) (reg : V) : Names V (n + 1) :=
  fun key => if key = reg then some 0 else (names key).map Fin.succ

/-- Choose the first occurrence in a finite context. -/
def first [DecidableEq V] (keys : Fin n → V) (key : V) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (keys i = key)

/-- Number internal labels first, using the same first-match order as named
lookup. A missing internal label must occur in the explicit exit list. -/
def labelIndex [DecidableEq K] (blocks : List (K × CFG.Block V K F)) (exits : List K)
    (label : K) : Option (Fin (blocks.length + exits.length)) :=
  match blocks.findFinIdx? (fun item => label == item.1) with
  | some i => some (i.castAdd exits.length)
  | none => (exits.findFinIdx? (fun exit => label == exit)).map (Fin.natAdd blocks.length)

/-- Compile a named value. Variables outside the binding map are rejected. -/
def value (names : Names V n) : Val V → Option (Tm Empty F n)
  | .var reg => (names reg).map .bv
  | .unit => some .unit
  | .pair left right => (value names left).bind fun a => (value names right).map (.pair a)

/-- The fragment uses variables, products, unit and primitives, including
primitives that return a sum for a case. Explicit injections and abort are
reserved for an interface with type annotations. -/
def operand (names : Names V n) : Op V F → Option (Tm Empty F n)
  | .val v => value names v
  | .app f a => (value names a).map (.op f)
  | .inl _ | .inr _ | .abort _ => none

variable [DecidableEq V]

def term (index : K → Option (Fin labels)) {n : Nat} (names : Names V n) :
    CFG.Term V K F → Option (LambdaSSA.Flat F labels n)
  | .br label arg => (index label).bind fun i => (value names arg).map (.br i)
  | .case op x left y right =>
      (operand names op).bind fun discr =>
        (term index (bindName names x) left).bind fun l =>
          (term index (bindName names y) right).map (.case discr l)

def body (index : K → Option (Fin labels)) {n : Nat} (names : Names V n) :
    CFG.Body V K F → Option (LambdaSSA.Flat F labels n)
  | .term tail => term index names tail
  | .let1 x op rest =>
      (operand names op).bind fun arg => (body index (bindName names x) rest).map (.let₁ arg)
  | .let2 x y op rest =>
      (operand names op).bind fun arg =>
        (body index (bindName (bindName names x) y) rest).map (.let₂ arg)

/-- The shared capture slots are invisible to named blocks. Only the packet
parameter at slot zero is in scope before the body executes. -/
def blockNames (param : V) : Names V (n + 1) :=
  bindName (fun _ => none) param

/-- Sequence a finite table while keeping its indexing. -/
def tabulate {A : Type v} : (count : Nat) → (Fin count → Option A) → Option (Fin count → A)
  | 0, _ => some Fin.elim0
  | count + 1, f =>
      (f 0).bind fun head =>
        (tabulate count fun i => f i.succ).map (Fin.cases head)

variable [DecidableEq K]

/-- Elaborate at an explicit block count equal to the length of the written
table. This keeps positional indices stable under primitive relabelling. -/
def elaborateAt (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    (count : Nat) (count_eq : graph.blocks.length = count) :
    Option (LambdaSSA.FiniteCFG F count exits.length n) :=
  let index := fun label => (labelIndex graph.blocks exits label).map
    (Fin.cast (congrArg (· + exits.length) count_eq))
  (body index (first captures) graph.entry).bind fun entry =>
    (tabulate count fun i =>
      let block := graph.blocks[(Fin.cast count_eq.symm i)].2
      body index (blockNames block.param) block.body).map fun blocks => ⟨entry, blocks⟩

/-- Convert the entire named table, preserving block order, with the specified
named inputs and external labels. -/
def elaborate (graph : CFG V K F) (exits : List K) (captures : Fin n → V) :
    Option (LambdaSSA.FiniteCFG F graph.blocks.length exits.length n) :=
  let index := labelIndex graph.blocks exits
  (body index (first captures) graph.entry).bind fun entry =>
    (tabulate graph.blocks.length fun i =>
      body index (blockNames graph.blocks[i].2.param) graph.blocks[i].2.body).map
      fun blocks => ⟨entry, blocks⟩

/-- Elaborate the actual output of named cyclic versioning. The supplied names
select the version-zero inputs of the entry. -/
def compile (source : CFG V K F) (exits : List K) (captures : Fin n → V) :
    Option (LambdaSSA.FiniteCFG F
      (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n) :=
  elaborate (CFG.Cyclic.Versioning.compile source) exits (fun i => (captures i, 0))

end Silmaril.Isotope.Bridge.NamedFlat
