module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.Pair.Thms

/-!
# Plays made of complete rounds

A *round* of `E ↠ F` is a question `q`, the complete calls `cs` it makes below (questions with
their answers) and its answer `a`; its moves are `ask q, (ask m, ans m n)…, ans q a`. The plays
used for instantiation runs are lists of rounds. This file builds such plays through the game
combinators:

* `zip_round`: a round of the upper strategy whose calls are served by rounds of the lower one
  is a round of the composite, with the lower rounds' calls (`Zip`);
* `mem_ofHandler_rounds`: rounds whose programs run to their answers (`Prog.Runs`) are plays of
  a handler;
* `mem_pair_rounds`: rounds on both sides of a pairing;
* `legal_rounds`: lists of rounds are legal.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games

variable {E F G : Sig.{0}}

/-- A complete call: a question and its answer. -/
abbrev Call (E : Sig.{0}) : Type := Σ m : E.Op, E.Ar m

/-- The events of complete calls. -/
def callEvs : List (Call E) → List (Ev E)
  | [] => []
  | ⟨m, n⟩ :: cs => .ask m :: .ans m n :: callEvs cs

theorem callEvs_append : ∀ (cs ds : List (Call E)), callEvs (cs ++ ds) = callEvs cs ++ callEvs ds
  | [], _ => rfl
  | ⟨_, _⟩ :: cs, ds => by simp only [List.cons_append, callEvs, callEvs_append cs ds]

/-- A round of `E ↠ F`: the question `q`, the complete calls `cs` below, the answer `a`. -/
structure Round (E F : Sig.{0}) where
  /-- The question. -/
  q : F.Op
  /-- The calls made below, with their answers. -/
  cs : List (Call E)
  /-- The answer. -/
  a : F.Ar q

/-- The moves of a round. -/
def Round.moves (r : Round E F) : List (Move E F) :=
  .inr (.ask r.q) :: ((callEvs r.cs).map .inl ++ [.inr (.ans r.q r.a)])

/-- A round seen from above: a complete call. -/
def Round.call (r : Round E F) : Call F := ⟨r.q, r.a⟩

/-- The moves of a list of rounds. -/
def roundsMoves : List (Round E F) → List (Move E F)
  | [] => []
  | r :: rs => r.moves ++ roundsMoves rs

theorem roundsMoves_append : ∀ (rs ss : List (Round E F)),
    roundsMoves (rs ++ ss) = roundsMoves rs ++ roundsMoves ss
  | [], _ => rfl
  | r :: rs, ss => by simp only [List.cons_append, roundsMoves, roundsMoves_append rs ss,
      List.append_assoc]

/-- The calls made by a list of rounds. -/
def allCalls : List (Round E F) → List (Call E)
  | [] => []
  | r :: rs => r.cs ++ allCalls rs

/-! ## Interaction -/

theorem zip_lefts {α β γ : Type} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) : ∀ l : List α, Zip (l.map .inl ++ s) t (l.map .inl ++ p)
  | [] => h
  | a :: l => .left a (zip_lefts h l)

/-- Calls served by rounds of the lower strategy. -/
theorem zip_serve {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ xs : List (Round E F),
      Zip (roundsMoves xs ++ s) ((callEvs (xs.map Round.call)).map .inl ++ t)
        ((callEvs (allCalls xs)).map .inl ++ p)
  | [] => h
  | ⟨q, cs, a⟩ :: xs => by
    have ih := zip_serve h xs
    simp only [roundsMoves, Round.moves, List.map_cons, Round.call, callEvs, allCalls,
      callEvs_append, List.map_append, List.cons_append, List.append_assoc, List.nil_append]
    refine .sync _ ?_
    refine zip_lefts ?_ _
    exact .sync _ ih

/-- **A round of the upper strategy whose calls are served by rounds of the lower one.** -/
theorem zip_round {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) (xs : List (Round E F)) (g : G.Op) (a : G.Ar g) :
    Zip (roundsMoves xs ++ s) ((Round.moves ⟨g, xs.map Round.call, a⟩) ++ t)
      ((Round.moves ⟨g, allCalls xs, a⟩) ++ p) := by
  simp only [Round.moves, List.cons_append, List.append_assoc]
  exact .right _ (zip_serve (.right _ h) xs)

/-- A single round served by rounds of the lower strategy. -/
theorem zip_round₀ (xs : List (Round E F)) (g : G.Op) (a : G.Ar g) :
    Zip (roundsMoves xs) (Round.moves ⟨g, xs.map Round.call, a⟩)
      (Round.moves ⟨g, allCalls xs, a⟩) := by
  simpa only [List.append_nil] using zip_round (Zip.nil (α := Ev E)) xs g a

/-! ## Handlers -/

/-- `Prog.Runs P cs a`: the program `P` makes the calls `cs` (answered as recorded) and returns
`a`. -/
inductive Prog.Runs {A : Type} : Prog E A → List (Call E) → A → Prop
  | pure (a : A) : Prog.Runs (.pure a) [] a
  | call {m : E.Op} {k : E.Ar m → Prog E A} {n : E.Ar m} {cs : List (Call E)} {a : A} :
      Prog.Runs (k n) cs a → Prog.Runs (.call m k) (⟨m, n⟩ :: cs) a

theorem handler_run_round {h : Handler E F} {q : F.Op} {P : Prog E (F.Ar q)}
    {cs : List (Call E)} {a : F.Ar q} (hr : Prog.Runs P cs a) :
    h.toReduction.toLTS.Run (.run q P) ((callEvs cs).map .inl ++ [.inr (.ans q a)]) .idle := by
  induction hr with
  | pure a => exact .vis (.ret rfl) (.nil _)
  | call _ ih => exact .vis (.call rfl) (.vis (.resume _ _ _ _) ih)

/-- **Rounds whose programs run to their answers are plays of a handler.** -/
theorem handler_run_rounds {h : Handler E F} :
    ∀ rs : List (Round E F), (∀ r ∈ rs, Prog.Runs (h r.q) r.cs r.a) →
      h.toReduction.toLTS.Run .idle (roundsMoves rs) .idle
  | [], _ => .nil _
  | r :: rs, hr => by
    simp only [roundsMoves, Round.moves, List.cons_append]
    exact .vis (.ask _) ((handler_run_round (hr r (.head _))).append
      (handler_run_rounds rs fun r' h' => hr r' (.tail _ h')))

theorem mem_ofHandler_rounds {h : Handler E F} (rs : List (Round E F))
    (hr : ∀ r ∈ rs, Prog.Runs (h r.q) r.cs r.a) : roundsMoves rs ∈ Strategy.ofHandler h :=
  Strategy.mem_ofHandler.2 ⟨_, handler_run_rounds rs hr⟩

/-! ## Legality -/

theorem path_callEvs_wait {q : F.Op} : ∀ cs : List (Call E),
    Path (.run q) ((callEvs cs).map (Sum.inl (β := Ev F))) (.run q)
  | [] => .nil _
  | ⟨m, n⟩ :: cs => .cons (.call q m) (.cons (.reply q m n) (path_callEvs_wait cs))

theorem path_round (r : Round E F) : Path .idle r.moves .idle :=
  .cons (.ask r.q) ((path_callEvs_wait r.cs).append (.cons (.ret r.q r.a) (.nil _)))

theorem path_rounds : ∀ rs : List (Round E F), Path .idle (roundsMoves rs) .idle
  | [] => .nil _
  | r :: rs => (path_round r).append (path_rounds rs)

theorem legal_rounds (rs : List (Round E F)) : Legal (roundsMoves rs) := ⟨_, path_rounds rs⟩

/-! ## Pairing -/

section Pair

variable {F₁ F₂ : Sig.{0}}

/-- A round of the left side of a pairing. -/
def Round.inl (r : Round E F₁) : Round E (F₁ ⊕ₛ F₂) := ⟨.inl r.q, r.cs, r.a⟩

/-- A round of the right side of a pairing. -/
def Round.inr (r : Round E F₂) : Round E (F₁ ⊕ₛ F₂) := ⟨.inr r.q, r.cs, r.a⟩

/-- A round on either side. -/
def sided : Round E F₁ ⊕ Round E F₂ → Round E (F₁ ⊕ₛ F₂)
  | .inl r => r.inl
  | .inr r => r.inr

theorem halves_lows (b : Bool) : ∀ (l : List (Ev E)) (s : List (Move E (F₁ ⊕ₛ F₂))),
    Split.halves b (l.map .inl ++ s) =
      (if b then ((Split.halves b s).1, l.map .inl ++ (Split.halves b s).2)
       else (l.map .inl ++ (Split.halves b s).1, (Split.halves b s).2))
  | [], s => by cases b <;> rfl
  | e :: l, s => by
    cases b <;> simp only [List.map_cons, List.cons_append, Split.halves, halves_lows _ l s,
      ite_true, ite_false, Bool.false_eq_true]

theorem halves_sided (b : Bool) (u : Round E F₁ ⊕ Round E F₂)
    (s : List (Move E (F₁ ⊕ₛ F₂))) :
    Split.halves b ((sided u).moves ++ s) =
      match u with
      | .inl r => (r.moves ++ (Split.halves false s).1, (Split.halves false s).2)
      | .inr r => ((Split.halves true s).1, r.moves ++ (Split.halves true s).2) := by
  rcases u with r | r
  · simp only [sided, Round.inl, Round.moves, List.cons_append, List.append_assoc,
      Split.halves, halves_lows, ite_false, Bool.false_eq_true, List.nil_append]
  · simp only [sided, Round.inr, Round.moves, List.cons_append, List.append_assoc,
      Split.halves, halves_lows, ite_true, List.nil_append]

/-- The left rounds. -/
def lefts : List (Round E F₁ ⊕ Round E F₂) → List (Round E F₁)
  | [] => []
  | .inl r :: us => r :: lefts us
  | .inr _ :: us => lefts us

/-- The right rounds. -/
def rights : List (Round E F₁ ⊕ Round E F₂) → List (Round E F₂)
  | [] => []
  | .inl _ :: us => rights us
  | .inr r :: us => r :: rights us

theorem halves_rounds (b : Bool) : ∀ us : List (Round E F₁ ⊕ Round E F₂),
    Split.halves b (roundsMoves (us.map sided)) =
      (roundsMoves (lefts us), roundsMoves (rights us))
  | [] => by cases b <;> rfl
  | u :: us => by
    simp only [List.map_cons, roundsMoves]
    rw [halves_sided]
    rcases u with r | r <;> simp only [halves_rounds _ us, lefts, rights, roundsMoves]

/-- **Rounds on both sides of a pairing.** -/
theorem mem_pair_rounds {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    (us : List (Round E F₁ ⊕ Round E F₂)) (h₁ : roundsMoves (lefts us) ∈ σ₁)
    (h₂ : roundsMoves (rights us) ∈ σ₂) : roundsMoves (us.map sided) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_rounds _, ?_, ?_⟩ <;> rw [halves_rounds]
  exacts [h₁, h₂]

theorem lefts_map_inl (l : List (Round E F₁)) :
    lefts (l.map (Sum.inl (β := Round E F₂))) = l := by
  induction l with
  | nil => rfl
  | cons r l ih => exact congrArg _ ih

theorem rights_map_inl (l : List (Round E F₁)) :
    rights (l.map (Sum.inl (β := Round E F₂))) = [] := by
  induction l with
  | nil => rfl
  | cons r l ih => exact ih

end Pair

end Silmaril.Proofs.Wasm.Component.InstSem
