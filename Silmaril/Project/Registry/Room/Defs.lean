module

public import Silmaril.Project.Registry.Predicate.Defs

/-!
# Silmaril projects: rooms (layer 4)

`silmaril room R := decl` registers a room over silmaril's `Room` (named, not imported:
`Silmaril.Logic.Institution.Room`; the handler is in `Registry.Institution.Defs`), and `silmaril problem N in R := φ` for a sentence
`φ : R.Sen` is the predicate `fun M => Silmaril.Project.Room.Problem R φ M` over the room's
models, so that THM is validity, SAT satisfiability, UNS unsatisfiability, CSA a countermodel,
and `(M := m)` is `m ⊨ φ`.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- silmaril's `Room` (named, so that the registry does not import it). -/
def roomName : Name := `Silmaril.Logic.Institution.Room

/-- Unfold `e` only through projections of definitions and `Cat.of`/`Bundled.of`, so that
`R.Sen` and the carrier of `R.Mod` print as the types the room was built from. -/
partial def peel (fuel : Nat) (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  let unfold (e : Expr) := do
    match fuel, ← unfoldDefinition? e with
    | fuel + 1, some e' => peel fuel e'
    | _, _ => return e
  match e with
  | .proj s i x =>
    match fuel, ← unfoldDefinition? (← whnfCore x) with
    | fuel + 1, some x' => peel fuel (.proj s i x')
    | _, _ => return e
  | _ =>
    let some c := e.getAppFn.constName? | return e
    if (← isProjectionFn c) || c == `CategoryTheory.Cat.of || c == `CategoryTheory.Bundled.of then
      unfold e
    else return e

/-- The sentence type and the model carrier of a room `R`. -/
def roomTypes (R : Expr) : MetaM (Expr × Expr) := do
  -- `R.Sat : ↑R.Mod → R.Sen → Prop`
  let .forallE _ mod (.forallE _ sen _ _) _ ← inferType (.proj roomName 2 R)
    | throwError "silmaril room: unexpected type of `Sat`"
  return (← peel 16 sen, ← peel 16 mod)

-- The handler of `room R := decl` is `Silmaril.Project.roomGraphHandler`
-- (`Registry.Institution.Defs`): rooms are the nodes of the room level of the logic graph, and may
-- be families `∀ x⃗, Room` (a problem needs a closed room, checked below).

/-- `silmaril problem N in R (k := v)* := φ`: for a registered room `R` and a sentence
`φ : R.Sen`, the problem `N` is the predicate `fun M => Silmaril.Project.Room.Problem R φ M` over the
room's models. The fields go to the problem's judgement. -/
syntax (name := silmarilRoomProblemCmd) "silmaril " "problem " silmarilName " in " silmarilName
  (ppSpace silmarilField)* " := " term : command

/-- Declare the problem `name` of the sentence `t : R.Sen` of the room `r`: the definition
`name := fun M => Silmaril.Project.Room.Problem R t M`, its `predicate` record, and the judgement
`fs`. Shared by `silmaril problem … in` and `@[problem "N" (room := R)]`. -/
def declareRoomProblem (name r : String) (t : Syntax) (fs : Fields) : CommandElabM Unit := do
  let decl ← fullName name
  liftTermElabM do
    let R := mkConst (← recordDecl "problem" "room" r)
    if let .forallE .. ← whnf (← inferType R) then
      throwError "silmaril problem: room {r} is a family of rooms; a problem needs a closed room \
        (register an instance `def x := {R} …` as a room)"
    let (sen, mod) ← roomTypes R
    let φ ← elabClosed t sen
    let value ← withLocalDeclD `M mod fun M => do
      mkLambdaFVars #[M] (← mkAppM `Silmaril.Project.Room.Problem #[R, φ, M])
    addPredicateDef decl value (← getRef)
  liftCoreM (registerPredicate name decl (some r))
  unless fs.values.isEmpty do runRecord "judgement" name fs

@[command_elab silmarilRoomProblemCmd]
def elabSilmarilRoomProblem : CommandElab := fun stx => do
  let fs ← liftCoreM (elabFields "problem" stx[5].getArgs)
  declareRoomProblem (nameOf stx[2]) (nameOf stx[4]) stx[7] fs

end Silmaril.Project
