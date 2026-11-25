module

public import Silmaril.SSA.RVSDG.Petri.Defs

public section

namespace Silmaril.SSA.RVSDG.Petri.Proofs

universe u w

variable {Ty : Type u} {F : Ty → Type w}

private theorem get_present {ts : Ports Ty} {t : Ty} (values : Tuple F ts) (p : Port ts t) :
    (values.map (fun _ => some)).get p = some (values.get p) := by
  induction p with
  | head => cases values; rfl
  | tail p ih => cases values with | cons _ rest => exact ih rest

theorem get_absent {ts : Ports Ty} {t : Ty} (p : Port ts t) :
    (absent (F := F) ts).get p = none := by
  induction p with
  | head => rfl
  | tail p ih => exact ih

/-- Each marked prefix place agrees with the corresponding numbered execution value. -/
@[expose] def Agrees : {past : List (Ports Ty)} → Tokens F past → Locals F past → Prop
  | [], _, _ => True
  | _ :: _, tokens, values =>
    (∀ t (p : Port _ t) (x : F t), tokens.1.get p = some x → values.1.get p = x) ∧
      Agrees tokens.2 values.2

private theorem agrees_get {past : List (Ports Ty)} {tokens : Tokens F past} {locals : Locals F past}
    (agrees : Agrees tokens locals) (i : Fin past.length) {t : Ty} (p : Port past[i] t) {x : F t}
    (h : (tokens.get i).get p = some x) : (locals.get i).get p = x := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    revert p h
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun p h => agrees.1 t p x h
    · exact fun p h => ih agrees.2 j p h

theorem agrees_snoc {past : List (Ports Ty)} {tokens : Tokens F past} {locals : Locals F past}
    (agrees : Agrees tokens locals) {ts : Ports Ty}
    {extra : Tuple (fun t => Option (F t)) ts} {values : Tuple F ts}
    (agreesExtra : ∀ t (p : Port ts t) (x : F t), extra.get p = some x → values.get p = x) :
    Agrees (tokens.snoc extra) (locals.snoc values) := by
  induction past with
  | nil => exact ⟨agreesExtra, trivial⟩
  | cons head tail ih => exact ⟨agrees.1, ih agrees.2⟩

theorem agrees_present {ts : Ports Ty} (values : Tuple F ts) {t : Ty}
    (p : Port ts t) {x : F t} (h : (values.map (fun _ => some)).get p = some x) :
    values.get p = x :=
  Option.some.inj ((get_present values p).symm.trans h)

theorem read_sound {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) {tokens : Tokens F past}
    {locals : Locals F past} (agrees : Agrees tokens locals) {xs : Tuple F users}
    (h : read wires entry tokens = some xs) : wires.read entry locals = xs := by
  induction wires with
  | nil => exact Option.some.inj h
  | cons source wires ih =>
    have consistent (x : F _) (hx : colour entry tokens source = some x) :
        (match source with | .arg p => entry.get p | .output i p => (locals.get i).get p) = x := by
      cases source with
      | arg p => exact Option.some.inj hx
      | output i p => exact agrees_get agrees i p hx
    simp only [read, Tuple.map, collect] at h
    split at h
    · next x rest hx hr =>
      have equalHead := consistent x hx
      have equalTail := ih hr
      cases h
      cases source <;> exact
        (congrArg (fun value => Tuple.cons value (Wires.read wires entry locals)) equalHead).trans
          (congrArg (Tuple.cons x) equalTail)
    · contradiction

/-- The token store with every colour of a prefix present. -/
@[expose] def full : {past : List (Ports Ty)} → Locals F past → Tokens F past
  | [], _ => PUnit.unit
  | _ :: _, locals => (locals.1.map fun _ => some, full locals.2)

theorem full_snoc {past : List (Ports Ty)} (locals : Locals F past)
    {ts : Ports Ty} (values : Tuple F ts) :
    full (locals.snoc values) = (full locals).snoc (values.map fun _ => some) := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun store => (locals.1.map fun _ => some, store)) (ih locals.2)

private theorem full_get {past : List (Ports Ty)} (locals : Locals F past) (i : Fin past.length) :
    (full locals).get i = (locals.get i).map (fun _ => some) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih locals.2 j

theorem read_full {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (locals : Locals F past) :
    read wires entry (full locals) = some (wires.read entry locals) := by
  induction wires with
  | nil => rfl
  | cons source wires ih =>
    simp only [read, Wires.read, Tuple.map, collect] at ih ⊢
    rw [ih]
    cases source with
    | arg p => rfl
    | output i p => simp only [colour, full_get, get_present]

end Silmaril.SSA.RVSDG.Petri.Proofs
