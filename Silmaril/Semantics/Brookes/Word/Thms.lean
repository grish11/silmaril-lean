module

public import Silmaril.Semantics.Brookes.Word.Defs
public import Silmaril.Semantics.Brookes.Thms
import Silmaril.Proofs.Semantics.Brookes.Word.Swaps

public section

namespace Silmaril.Semantics.Brookes.Word

universe u v w z

variable {Letter : Type u} {Store : Type v} {X : Type w} {Y : Type z}
variable {letter : Letter → Command Store} {independent : Letter → Letter → Prop}

theorem eval_nil (letter : Letter → Command Store) : eval letter [] = Command.skip := rfl

theorem eval_singleton (letter : Letter → Command Store) (a : Letter) :
    eval letter [a] = letter a := Command.seq_skip _

theorem eval_pair (letter : Letter → Command Store) (a b : Letter) :
    eval letter [a, b] = Command.seq (letter a) (letter b) :=
  congrArg (Command.seq (letter a)) (eval_singleton letter b)

theorem eval_append (letter : Letter → Command Store) (left right : List Letter) :
    eval letter (left ++ right) = Command.seq (eval letter left) (eval letter right) :=
  Proofs.Semantics.Brookes.Word.eval_append letter left right

theorem eval_of_swap (commutes : Commutes independent letter) {first second : List Letter}
    (swap : Swap independent first second) : eval letter first = eval letter second :=
  Proofs.Semantics.Brookes.Word.eval_of_swap commutes swap

theorem endpoints_skip : endpoints (Command.skip : Command Store) = Eq :=
  Proofs.Semantics.Brookes.Word.endpoints_skip

theorem endpoints_seq (p q : Command Store) :
    endpoints (Command.seq p q) = fun s t => ∃ m, endpoints p s m ∧ endpoints q m t :=
  Proofs.Semantics.Brookes.Word.endpoints_seq p q

theorem endpoints_of_swap (commutes : CommutesAtEndpoints independent letter)
    {first second : List Letter} (swap : Swap independent first second) :
    endpoints (eval letter first) = endpoints (eval letter second) :=
  Proofs.Semantics.Brookes.Word.endpoints_of_swap commutes swap

/-- An interpretation of the adjacent-swap quotient into full Brookes commands. -/
@[expose] def lift (commutes : Commutes independent letter) : Quot (Swap independent) → Command Store :=
  Quot.lift (eval letter) (fun _ _ swap => eval_of_swap commutes swap)

/-- An interpretation of the adjacent-swap quotient into store relations. -/
@[expose] def liftEndpoints (commutes : CommutesAtEndpoints independent letter) :
    Quot (Swap independent) → Store → Store → Prop :=
  Quot.lift (fun word => endpoints (eval letter word)) (fun _ _ swap => endpoints_of_swap commutes swap)

theorem lift_mk (commutes : Commutes independent letter) (word : List Letter) :
    lift commutes (Quot.mk _ word) = eval letter word := rfl

theorem liftEndpoints_mk (commutes : CommutesAtEndpoints independent letter) (word : List Letter) :
    liftEndpoints commutes (Quot.mk _ word) = endpoints (eval letter word) := rfl

theorem lift_append (commutes : Commutes independent letter) (left right : List Letter) :
    lift commutes (Quot.mk _ (left ++ right)) =
      Command.seq (lift commutes (Quot.mk _ left)) (lift commutes (Quot.mk _ right)) :=
  eval_append letter left right

theorem liftEndpoints_append (commutes : CommutesAtEndpoints independent letter)
    (left right : List Letter) :
    liftEndpoints commutes (Quot.mk _ (left ++ right)) = fun s t =>
      ∃ m, liftEndpoints commutes (Quot.mk _ left) s m ∧ liftEndpoints commutes (Quot.mk _ right) m t :=
  (congrArg endpoints (eval_append letter left right)).trans (endpoints_seq _ _)

/-- A factorization through the swap quotient forces the open equations on letters. -/
theorem commutes_of_lift (f : Quot (Swap independent) → Command Store)
    (h : ∀ word, f (Quot.mk _ word) = eval letter word) : Commutes independent letter := by
  intro a b hab
  simpa only [h, List.nil_append, eval_pair] using
    congrArg f (Quot.sound (Swap.adjacent (independent := independent) [] [] hab))

/-- A factorization through the swap quotient forces the endpoint equations on letters. -/
theorem commutesAtEndpoints_of_lift (f : Quot (Swap independent) → Store → Store → Prop)
    (h : ∀ word, f (Quot.mk _ word) = endpoints (eval letter word)) :
    CommutesAtEndpoints independent letter := by
  intro a b hab
  simpa only [h, List.nil_append, eval_pair] using
    congrArg f (Quot.sound (Swap.adjacent (independent := independent) [] [] hab))

/-- Disjoint product factors commute at endpoints, including partial or
nondeterministic relations on either factor. -/
theorem product_commutes_at_endpoints (p q : Command (X × Y))
    (left : X → X → Prop) (right : Y → Y → Prop)
    (hp : endpoints p = fun s t => left s.1 t.1 ∧ s.2 = t.2)
    (hq : endpoints q = fun s t => s.1 = t.1 ∧ right s.2 t.2) :
    endpoints (Command.seq p q) = endpoints (Command.seq q p) :=
  Proofs.Semantics.Brookes.Word.product_commutes_at_endpoints p q left right hp hq

end Silmaril.Semantics.Brookes.Word
