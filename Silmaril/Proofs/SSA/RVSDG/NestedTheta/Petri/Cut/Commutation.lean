module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Commutation.Proofs

open RVSDG.Petri (Tokens absent colour collect)
open Relation (ReflTransGen)

universe u v w

section Colours
variable {Ty : Type u} {F : Ty → Type w}

private abbrev Contains {ports : Ports Ty}
    (before after : Tuple (fun t => Option (F t)) ports) : Prop :=
  ∀ t (port : Port ports t) x, before.get port = some x → after.get port = some x

private def Keeps : {past : List (Ports Ty)} → Tokens F past → Tokens F past → Prop
  | [], _, _ => True
  | _ :: _, before, after => Contains before.1 after.1 ∧ Keeps before.2 after.2

private theorem Keeps.refl {past : List (Ports Ty)} (tokens : Tokens F past) : Keeps tokens tokens := by
  induction past with
  | nil => trivial
  | cons _ _ ih => exact ⟨fun _ _ _ h => h, ih tokens.2⟩

private theorem Keeps.trans {past : List (Ports Ty)} {a b c : Tokens F past}
    (ab : Keeps a b) (bc : Keeps b c) : Keeps a c := by
  induction past with
  | nil => trivial
  | cons _ _ ih => exact ⟨fun t p x h => bc.1 t p x (ab.1 t p x h), ih ab.2 bc.2⟩

private theorem Keeps.snoc {past : List (Ports Ty)} {a b : Tokens F past}
    {ports : Ports Ty} {x y : Tuple (fun t => Option (F t)) ports}
    (old : Keeps a b) (new : Contains x y) : Keeps (a.snoc x) (b.snoc y) := by
  induction past with
  | nil => exact ⟨new, trivial⟩
  | cons _ _ ih => exact ⟨old.1, ih old.2⟩

private theorem Keeps.get {past : List (Ports Ty)} {a b : Tokens F past} (old : Keeps a b)
    (i : Fin past.length) : Contains (a.get i) (b.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases old.1 (fun j => ih old.2 j) i

private theorem contains_absent {ports : Ports Ty} (out : Tuple (fun t => Option (F t)) ports) :
    Contains (absent ports) out := by
  have missing {ts : Ports Ty} {t : Ty} (port : Port ts t) : (absent (F := F) ts).get port = none := by
    induction port with
    | head => rfl
    | tail _ ih => exact ih
  intro _ port _ impossible
  rw [missing port] at impossible
  cases impossible

private theorem read_kept {args users : Ports Ty} {past : List (Ports Ty)} (wires : Wires args past users)
    (entry : Tuple F args) {before after : Tokens F past} (keeps : Keeps before after)
    {result : Tuple F users} (read : RVSDG.Petri.read wires entry before = some result) :
    RVSDG.Petri.read wires entry after = some result := by
  induction wires with
  | nil => exact read
  | cons wire rest ih =>
    simp only [RVSDG.Petri.read, Tuple.map, collect] at read ⊢
    split at read
    · next value values haveHead haveTail =>
      have head : colour entry after wire = some value := by
        cases wire with
        | arg p => exact haveHead
        | output i p => exact keeps.get i _ p value haveHead
      have tail : collect (rest.map fun _ => colour entry after) = some values := ih haveTail
      rw [head, tail]
      exact read
    · cases read

end Colours

section Firings
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}
variable (cut : Cut front whole tail) (m : Model.{u, v, w} Op)

private theorem fire_kept {term : Term Op args past wholeSigs outs}
    {entry : Tuple m.Val args} {old new : Tokens m.Val past}
    {before after : Marking m term}
    (step : Fire m term entry old before after) (more : Keeps old new) :
    Fire m term entry new before after := by
  induction step with
  | primitive ready ran => exact .primitive (read_kept _ _ more ready) ran
  | enter ready tag => exact .enter (read_kept _ _ more ready) tag
  | advance fired => exact .advance fired
  | commit ready tag => exact .commit ready tag
  | restart ready tag entered => exact .restart ready tag entered
  | later fired ih => exact .later (ih (more.snoc (fun _ _ _ h => h)))

private theorem tokens_kept (mark : Marking m front) {old new : Tokens m.Val past}
    (more : Keeps old new) :
    Keeps (cut.tokens m old mark) (cut.tokens m new mark) := by
  induction cut with
  | stop => exact more
  | bind _ _ _ ih => exact ih mark.2 (more.snoc (fun _ _ _ h => h))

private theorem tokens_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m front} (step : Fire m front entry tokens before after) :
    Keeps (cut.tokens m tokens before) (cut.tokens m tokens after) := by
  induction cut with
  | stop => cases step
  | bind _ _ inner ih =>
    cases step
    case later fired => exact ih _ fired
    all_goals exact tokens_kept inner m _ ((Keeps.refl tokens).snoc (contains_absent _))

/-- A continuation firing can use the later prefix store. Every colour
it could read before is still present at the same typed place. -/
theorem tail_after_prefix (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m front}
    (prefixSteps : ReflTransGen (Fire m front entry tokens) before after)
    {a b : Marking m tail} (step : Fire m tail entry (cut.tokens m tokens before) a b) :
    Fire m tail entry (cut.tokens m tokens after) a b := by
  have preserved : Keeps (cut.tokens m tokens before) (cut.tokens m tokens after) := by
    clear step
    induction prefixSteps with
    | refl => exact Keeps.refl _
    | tail _ fired ih => exact ih.trans (tokens_step cut m entry tokens fired)
  exact fire_kept m step preserved

end Firings
end Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Commutation.Proofs
