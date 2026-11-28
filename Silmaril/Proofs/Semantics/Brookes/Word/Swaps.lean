module

public import Silmaril.Semantics.Brookes.Word.Defs
public import Silmaril.Semantics.Brookes.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.Word

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.Word

universe u v w z

variable {Letter : Type u} {Store : Type v} {X : Type w} {Y : Type z}
variable {letter : Letter → Command Store} {independent : Letter → Letter → Prop}

theorem eval_append (letter : Letter → Command Store) (left right : List Letter) :
    eval letter (left ++ right) = Command.seq (eval letter left) (eval letter right) := by
  induction left with
  | nil => exact (Command.skip_seq _).symm
  | cons a rest ih =>
    rw [List.cons_append, eval, ih, eval, Command.seq_assoc]

private theorem eval_pair_context (pre post : List Letter) (a b : Letter) :
    eval letter (pre ++ a :: b :: post) =
      Command.seq (eval letter pre) (Command.seq (Command.seq (letter a) (letter b))
        (eval letter post)) := by
  rw [eval_append]
  simp only [eval, Command.seq_assoc]

theorem eval_of_swap (commutes : Commutes independent letter) {first second : List Letter}
    (swap : Swap independent first second) : eval letter first = eval letter second := by
  cases swap with
  | adjacent pre post h => simp only [eval_pair_context, commutes h]

theorem endpoints_skip : endpoints (Command.skip : Command Store) = Eq := by
  funext s t
  apply propext
  exact Behavior.atomic_completes_iff.trans ⟨And.left, fun h => ⟨h, rfl⟩⟩

theorem endpoints_seq (p q : Command Store) :
    endpoints (Command.seq p q) = fun s t => ∃ m, endpoints p s m ∧ endpoints q m t := by
  funext s t
  exact propext Command.seq_completes_iff

private theorem endpoints_seq_congr {p p' q q' : Command Store}
    (hp : endpoints p = endpoints p') (hq : endpoints q = endpoints q') :
    endpoints (Command.seq p q) = endpoints (Command.seq p' q') := by
  rw [endpoints_seq, endpoints_seq, hp, hq]

theorem endpoints_of_swap (commutes : CommutesAtEndpoints independent letter)
    {first second : List Letter} (swap : Swap independent first second) :
    endpoints (eval letter first) = endpoints (eval letter second) := by
  cases swap with
  | adjacent pre post h =>
    simp only [eval_pair_context]
    exact endpoints_seq_congr rfl (endpoints_seq_congr (commutes h) rfl)

theorem product_commutes_at_endpoints (p q : Command (X × Y))
    (left : X → X → Prop) (right : Y → Y → Prop)
    (hp : endpoints p = fun s t => left s.1 t.1 ∧ s.2 = t.2)
    (hq : endpoints q = fun s t => s.1 = t.1 ∧ right s.2 t.2) :
    endpoints (Command.seq p q) = endpoints (Command.seq q p) := by
  rw [endpoints_seq p q, endpoints_seq q p, hp, hq]
  funext s t
  apply propext
  constructor
  · rintro ⟨m, ⟨hl, hy⟩, ⟨hx, hr⟩⟩
    exact ⟨(s.1, t.2), ⟨rfl, hy.symm ▸ hr⟩, ⟨hx ▸ hl, rfl⟩⟩
  · rintro ⟨m, ⟨hx, hr⟩, ⟨hl, hy⟩⟩
    exact ⟨(t.1, s.2), ⟨hx.symm ▸ hl, rfl⟩, ⟨rfl, hy ▸ hr⟩⟩

end Silmaril.Proofs.Semantics.Brookes.Word
