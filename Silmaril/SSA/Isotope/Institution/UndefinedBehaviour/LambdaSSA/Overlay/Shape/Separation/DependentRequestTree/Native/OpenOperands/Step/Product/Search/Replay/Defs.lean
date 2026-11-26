module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs

/-! # Typed interpreter scripts for shared guarded reply paths -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet pack)

universe u

namespace InterpreterScript

variable {Φ : Type u} [HasTy Φ Syntax.Ty]

/-- The key is exactly an input of the native primitive interpreter. -/
structure Query (Φ : Type u) [HasTy Φ Syntax.Ty] (states : Nat) where
  op : Φ
  arg : Syntax.Payload (instrSrc op)
  state : Fin states

variable {states : Nat}

def Query.key (q : Query Φ states) : Φ × Value Unit × Fin states :=
  (q.op, q.arg.val, q.state)

theorem Query.key_injective : Function.Injective (Query.key (Φ := Φ) (states := states)) := by
  rintro ⟨f, a, s⟩ ⟨g, b, t⟩ eq
  change (f, a.val, s) = (g, b.val, t) at eq
  obtain ⟨rfl, rest⟩ := Prod.mk.inj eq
  obtain ⟨args, rfl⟩ := Prod.mk.inj rest
  exact congrArg (fun x => Query.mk f x s) (Subtype.ext args)

instance [DecidableEq Φ] : DecidableEq (Query Φ states) :=
  fun a b => decidable_of_iff (a.key = b.key) Query.key_injective.eq_iff

abbrev Row (Φ : Type u) [HasTy Φ Syntax.Ty] (states : Nat) :=
  Σ q : Query Φ states, Syntax.Reply (instrTrg q.op) states

def Query.read (prim : Syntax.Primitives Φ states) (q : Query Φ states) :
    Syntax.Reply (instrTrg q.op) states :=
  prim q.op q.arg q.state

def Realizes (prim : Syntax.Primitives Φ states) (rows : List (Row Φ states)) : Prop :=
  ∀ row ∈ rows, row.1.read prim = row.2

/-- A repeated key must agree on the entire native answer, including its
final state. Its dependent answer type is transported along key equality. -/
def Consistent (rows : List (Row Φ states)) : Prop :=
  ∀ a ∈ rows, ∀ b ∈ rows, ∀ same : a.1 = b.1,
    (same ▸ a.2 : Syntax.Reply (instrTrg b.1.op) states) = b.2

def Row.lookup [DecidableEq Φ] (q : Query Φ states) (row : Row Φ states) :
    Option (Syntax.Reply (instrTrg q.op) states) :=
  if same : row.1 = q then some (same ▸ row.2) else none

/-- Extend a finite script by first-match lookup and a total fallback. The
fallback can use a typed reply when available, or ordinary divergence. -/
def extend [DecidableEq Φ] (rows : List (Row Φ states)) (fallback : Syntax.Primitives Φ states) :
    Syntax.Primitives Φ states :=
  fun f a s => (rows.findSome? (Row.lookup ⟨f, a, s⟩)).getD (fallback f a s)

def Row.success {S : RequestSignature Φ} (q : Query Φ states) (reply : Packet (S.replies q.op))
    (final : Fin states) : Row Φ states :=
  ⟨q, .ret (cast (congrArg Syntax.Payload (S.target q.op).symm) (pack reply)) final⟩

end InterpreterScript

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}

/-- A scheduled shared path records the actual synchronized request at
each edge, with an explicit list of reply states. -/
inductive ScheduledPath (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (start : ProductConfig R T) (initial : Fin states) :
    List (ProductEdge S R T) → List (Fin states) → ProductConfig R T → Fin states → List (InterpreterScript.Row Φ states) → Prop where
  | start : ScheduledPath g h caller caller' start initial [] [] start initial []
  | step {past stores p s rows f arg next next'} (earlier : ScheduledPath g h caller caller' start initial past stores p s rows)
      (left : g.head caller p.1 = .request f arg next) (right : h.head caller' p.2 = .request f arg next')
      (reply : Packet (S.replies f)) (t : Fin states) :
      ScheduledPath g h caller caller' start initial
        (past ++ [(⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2)]) (stores ++ [t])
        (next reply.1 reply.2, next' reply.1 reply.2) t (rows ++ [InterpreterScript.Row.success ⟨f, arg, s⟩ reply t])

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
