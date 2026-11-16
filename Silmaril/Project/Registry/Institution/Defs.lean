module

public import Silmaril.Project.Registry.Room.Defs

/-!
# Silmaril projects: the logic graph (layer 4)

Record kinds for the **logic graph** (`docs/projects/logic-graph.md`): institutions as nodes,
comorphisms and morphisms as typed, directed edges between them, and, one level down, rooms (an
institution at one signature, `Silmaril.Project.Registry.Room.Defs`) with corridors between them.
Every record names a Lean declaration whose type Lean checks; the endpoints of an edge are not
written by hand but found by Lean among the registered nodes, so the graph the explorer draws is
the graph of the declarations.

| kind | Lean checks | Lean fills |
|---|---|---|
| `institution N := I` | `I : Silmaril.Logic.Institution.Inst` (any universe levels) | `type`, `levels`, `doc` (docstring) |
| `comorphism N := f` | `f : Inst.CoHom A B` with `A`, `B` registered institutions | `from`, `to`, `type`, `levels`, `doc` |
| `morphism N := f` | `f : Inst.Hom A B` with `A`, `B` registered institutions | `from`, `to`, `type`, `levels`, `doc` |
| `corridor N := c` | `c : Silmaril.Logic.Institution.Corridor R₁ R₂` with `R₁`, `R₂` registered rooms | `from`, `to`, `type`, `levels`, `doc` |
| `institution`, `room` | not defined exactly as an already registered one (one node per institution or room) | |
| any of the five | not a generic construction: no binder ranges over institutions, rooms or maps (`genericBinderHeads`) | |
| `logic_audit (prefix := P)` | — | one record per declaration under `P` whose type is one of the five |

**Directions.** Both kinds of institution edge are recorded from `A` to `B` as Lean writes the
type, `Inst.CoHom A B` or `Inst.Hom A B`, and the signature functor always goes `Φ : Sign_A ⥤ Sign_B`.
The difference is the direction of the rest:

* a *comorphism* `(Φ, ρ) : A → B` (a logic translation, Goguen–Roşu Definition 4.2) translates
  sentences forwards `Sen_A Σ → Sen_B (Φ Σ)` and models backwards `Mod_B (Φ Σ) → Mod_A Σ`;
* a *morphism* `(Φ, η) : A → B` (a logic projection, Goguen–Burstall Definition 13) translates
  sentences backwards `Sen_B (Φ Σ) → Sen_A Σ` and models forwards `Mod_A Σ → Mod_B (Φ Σ)`;
* a *corridor* `(α, β) : R₁ → R₂` is a comorphism at one signature: sentences forwards, models
  backwards.

**Endpoints.** `(from := A)` and `(to := B)` may be given; otherwise Lean finds them: the
registered node whose declaration is the endpoint of the type up to reducible unfolding (with
fresh universe levels). An endpoint that is not registered is an error, and so is one that
is an instance of two registered nodes, unless one of them is the endpoint's own head constant
(a family defined as an instance of another), or else the one whose own definition is the
endpoint up to reducible unfolding (not an alias of it).  A given endpoint is checked at default transparency.

**Facts.** `(facts := [p, …])` lists theorems about the edge. Lean checks that each states a
known property *of this declaration* and records it with the theorem's axioms:

| property | statement |
|---|---|
| `model_expansive` | `Inst.CoHom.ModelExpansive f` (every model translation is surjective: borrowing) |
| `sound` | `Inst.Hom.Sound f` (every model translation of a morphism is surjective) |
| `model_expansive` | `Corridor.ModelExpansive c` |

A fact about a family holds at every argument unless it records `at`: the arguments of the one
instance it is about. A property that is not listed is not claimed: the registry records no
property as a tag.

**Hets.** `(hets := "Name")` relates a node or an edge to a logic or comorphism of the Hets logic
graph (`silmaril/logic-graph/hets.toml`), and `(hets_relation := r)` says how: `corresponds`
(the same logic or translation, as far as the Lean definition goes), `fragment` (a fragment of
it) or `related` (a comparable construction, not the same one). `sil project check` checks the
name against the pinned Hets list. Free text (`title`, `doc`, `source`, `scope`) is kept as written.

**Audit.** `silmaril logic_audit (prefix := P)` scans every declaration of the environment under
`P` that is not a theorem, and whose type, after its binders, is (up to reducible unfolding) an
institution, comorphism, morphism, room or corridor. It records each with its arity (the number of
binders: `0` is a closed declaration, more is a family), its module and the record that registers
it, if any, and whether it is `generic`: a construction over an arbitrary institution, room or map
(a binder's type mentions one, as in `Inst.th A` or `CoHom.id A`), which no registry entry can
name an endpoint of. The explorer reads it as the list of what the registry omits. Run it last, in a module
that imports every registration.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

/-- silmaril's institutions (named, not imported, as `roomName`). -/
def instName : Name := `Silmaril.Logic.Institution.Inst
/-- Institution comorphisms `Inst.CoHom A B`. -/
def coHomName : Name := `Silmaril.Logic.Institution.Inst.CoHom
/-- Institution morphisms `Inst.Hom A B`. -/
def homName : Name := `Silmaril.Logic.Institution.Inst.Hom
/-- Corridors `Corridor R₁ R₂`. -/
def corridorName : Name := `Silmaril.Logic.Institution.Corridor

/-- The known facts: `(record kind, property head, property name)`. -/
def logicFacts : List (String × Name × String) := [
  ("comorphism", `Silmaril.Logic.Institution.Inst.CoHom.ModelExpansive, "model_expansive"),
  ("morphism", `Silmaril.Logic.Institution.Inst.Hom.Sound, "sound"),
  ("corridor", `Silmaril.Logic.Institution.Corridor.ModelExpansive, "model_expansive")]

/-- What an institution-graph record kind declares: `(type head, endpoint kind)`. -/
def logicKindHead : String → Option (Name × Option String)
  | "institution" => some (instName, none)
  | "comorphism" => some (coHomName, some "institution")
  | "morphism" => some (homName, some "institution")
  | "room" => some (roomName, none)
  | "corridor" => some (corridorName, some "room")
  | _ => none

/-- The record kind of a type head. -/
def logicKindOf? (head : Name) : Option String :=
  ["institution", "comorphism", "morphism", "room", "corridor"].find? fun k =>
    (logicKindHead k).any (·.1 == head)

/-- Pretty-print with full names and without field notation, on one line. -/
def ppLogic (e : Expr) : MetaM String :=
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.fieldNotation.generalized false) do
    return (← ppExpr e).pretty 100000

/-- Run `k xs body` on the binders `xs` of the type of `d` (at its universe parameters) and its body,
unfolded until its head is not a definition (so that `Institution₁` is `Inst.{1, 0, 0, 0, 0}` and
`R₁ ⟶ R₂` in `Room` is `Corridor R₁ R₂`). -/
def logicTelescope {α : Type} (d : Name) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let c := mkConst d ((← getConstInfo d).levelParams.map Level.param)
  forallTelescopeReducing (← inferType c) fun xs body => do k xs (← whnf body)

/-- Whether `e` is an instance of the registered declaration `c`: `c ?x₁ … ?xₙ` for its binders
`xᵢ`, up to `isDefEq` at transparency `t`. Returns the printed arguments (the state is restored). -/
def instanceOf? (e : Expr) (c : Name) (t : TransparencyMode) : MetaM (Option (Array String)) :=
  withoutModifyingState do
    let cc ← mkConstWithFreshMVarLevels c
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType cc)
    if ← withTransparency t (isDefEq e (mkAppN cc mvs)) then
      return some (← mvs.mapM fun m => do ppLogic (← instantiateMVars m))
    return none

/-- The registered `ofKind` records whose declaration `e` is an instance of, with the arguments. -/
def registeredMatches (ofKind : String) (e : Expr) (only? : Option String)
    (t : TransparencyMode) : MetaM (Array (String × Array String)) := do
  let env ← getEnv
  let mut out := #[]
  for r in records env do
    unless r.kind == ofKind do continue
    if let some o := only? then unless r.name == o do continue
    let some d := r.str? "decl" | continue
    let some _ := env.find? d.toName | continue
    if let some args ← instanceOf? e d.toName t then out := out.push (r.name, args)
  return out

/-- Resolve one endpoint `e` of a `kind` record among the registered `ofKind` records: reducible
unfolding first, then default unfolding; a given name is checked at default unfolding. -/
def resolveEndpoint (kind side ofKind : String) (e : Expr) (given? : Option String) :
    MetaM (String × Array String) := do
  match given? with
  | some g =>
    let some _ := findRecord? (← getEnv) ofKind g
      | throwError "silmaril {kind}: `({side} := {g})`: no `silmaril {ofKind} {g}` is declared or imported"
    let ms ← registeredMatches ofKind e (some g) .default
    let some m := ms[0]? | throwError "silmaril {kind}: `({side} := {g})`, but the {side} endpoint of \
      its type is{indentExpr e}\nwhich is not an instance of the declaration of {ofKind} {g}"
    return m
  | none =>
    let mut ms ← registeredMatches ofKind e none .reducible
    if ms.isEmpty then ms ← registeredMatches ofKind e none .default
    -- a family defined as an instance of another matches both: prefer the endpoint's own head
    if ms.size > 1 then
      let env ← getEnv
      let head := (← instantiateMVars e).getAppFn.constName?
      let own := ms.filter fun (n, _) =>
        ((findRecord? env ofKind n).bind (·.str? "decl")).map String.toName == head
      if own.size == 1 then ms := own
    -- aliases (`def B := A`) match too: prefer the declaration whose own definition is the
    -- endpoint up to reducible unfolding
    if ms.size > 1 then
      let env ← getEnv
      let mut direct := #[]
      for m in ms do
        let some d := (findRecord? env ofKind m.1).bind (·.str? "decl") | continue
        let some info := env.find? d.toName | continue
        let some v := info.value? | continue
        let ok ← withoutModifyingState do
          let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
          let v := v.instantiateLevelParams info.levelParams lvls
          let (_, _, body) ← lambdaMetaTelescope v
          withTransparency .reducible (isDefEq e body)
        if ok then direct := direct.push m
      if direct.size == 1 then ms := direct
    match ms.toList with
    | [m] => return m
    | [] => throwError "silmaril {kind}: the {side} endpoint{indentExpr e}\nis not a registered \
        {ofKind}: register it with `silmaril {ofKind} <name> := <decl>` first, or give \
        `({side} := <name>)`"
    | ns => throwError "silmaril {kind}: the {side} endpoint{indentExpr e}\nis an instance of several \
        registered {ofKind}s: {ns.map (·.1)}; give `({side} := <name>)`"

/-- The theorems of `(facts := [p, …])`, checked: each states, for all its arguments, a known
property of an instance of `subject`. -/
def checkFacts (kind : String) (subject : Name) (fs : Fields) : TermElabM (Option Json) := do
  let some v := fs.get? "facts" | return none
  let .arr ps := v | throwError "silmaril {kind}: `facts` is a list of theorems"
  let mut out := #[]
  for p in ps do
    let .str s := p | throwError "silmaril {kind}: `facts` is a list of theorems"
    let pn ← realizeGlobalConstNoOverload (mkIdent s.toName)
    unless ← isProp (← getConstInfo pn).type do
      throwError "silmaril {kind}: fact {pn} is not a theorem"
    let prop? ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels pn)) fun _ ty => do
      let ty ← whnfR ty
      let some head := ty.getAppFn.constName? | return none
      let some (_, _, prop) := logicFacts.find? fun (k, h, _) => k == kind && h == head | return none
      let e := ty.appArg!
      let some args ← instanceOf? e subject .default
        | throwError "silmaril {kind}: fact {pn} is about{indentExpr e}\nnot about {subject}"
      -- general: about the family at distinct variables of the theorem; else at an instance
      let xs := e.getAppArgs
      let general := e.getAppFn.isConstOf subject && xs.all Expr.isFVar &&
        (xs.map Expr.fvarId!).toList.eraseDups.length == xs.size
      return some (prop, if general then none else some (" ".intercalate args.toList))
    let some (prop, at?) := prop? | throwError "silmaril {kind}: fact {pn} does not state a known property; \
      the known properties of a {kind} are {(logicFacts.filter (·.1 == kind)).map (·.2.1)}"
    let axioms := ((← collectAxioms pn).map toString).qsort (· < ·)
    out := out.push (Json.mkObj ([("property", .str prop), ("proof", .str pn.toString),
      ("axioms", toJson axioms)] ++ (at?.map fun a => ("at", Json.str a)).toList))
  return some (.arr out)

/-- The universe parameters of a declaration, space-separated. -/
def levelsOf (d : Name) : CoreM String := do
  return " ".intercalate ((← getConstInfo d).levelParams.map toString)

/-- The binders of a family, printed: `(P : Type) {n : ℕ}`. -/
def paramsOf (xs : Array Expr) : MetaM String := do
  let ps ← xs.mapM fun x => do
    let d ← x.fvarId!.getDecl
    let (l, r) := match d.binderInfo with
      | .implicit => ("{", "}") | .instImplicit => ("[", "]") | .strictImplicit => ("⦃", "⦄")
      | _ => ("(", ")")
    return s!"{l}{d.userName.eraseMacroScopes} : {← ppLogic d.type}{r}"
  return " ".intercalate ps.toList

/-- The institution a room is a fiber of, and the signature: an instance `A.I.obj S` of a
registered institution `A`, found up to reducible unfolding, else default unfolding. -/
def roomInstitution? (R : Expr) (given? : Option String) : MetaM (Option (String × String)) := do
  let env ← getEnv
  for r in records env do
    unless r.kind == "institution" do continue
    if let some g := given? then unless r.name == g do continue
    let some d := r.str? "decl" | continue
    let some _ := env.find? d.toName | continue
    let found ← withoutModifyingState <| observing? (α := Option String) do
      let cc ← mkConstWithFreshMVarLevels d.toName
      let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType cc)
      let A := mkAppN cc mvs
      let sign ← whnf (← mkAppM `Silmaril.Logic.Institution.Inst.Sign #[A])
      let S ← mkFreshExprMVar sign
      let I ← mkAppM `Silmaril.Logic.Institution.Inst.I #[A]
      let obj ← mkAppM `Prefunctor.obj #[← mkAppM `CategoryTheory.Functor.toPrefunctor #[I], S]
      if ← withTransparency .reducible (isDefEq R obj) <||> withTransparency .default (isDefEq R obj) then
        return some (← ppLogic (← instantiateMVars S))
      return none
    if let some (some s) := found then return some (r.name, s)
  if let some g := given? then
    throwError "silmaril room: `(institution := {g})`, but the room{indentExpr R}\nis not `I.obj S` for \
      the institution {g}"
  return none

/-- Types that make a binder *generic*: a declaration over an arbitrary institution, room, map
between them or diagram of them is a construction, not a node or an edge of the graph. -/
def genericBinderHeads : List Name := [instName, roomName, coHomName, homName, corridorName,
  `Silmaril.Logic.Institution.CoIns, `Silmaril.Logic.Institution.Ins,
  `Silmaril.Logic.Institution.LogicGraph, `Silmaril.Logic.Institution.ClassicInstitution,
  `Silmaril.Logic.Institution.Theory, `Silmaril.Logic.Institution.Metatheory.LogicalSystem,
  `Silmaril.Inst.GraphSpec, `Silmaril.Inst.CoEdge, `Silmaril.Inst.MorEdge, `Silmaril.Inst.Plain]

/-- Whether a binder type mentions (up to reducible unfolding at its head) one of
`genericBinderHeads`. -/
def genericBinder (ty : Expr) : MetaM Bool := do
  let ty' ← whnfR ty
  let hit (e : Expr) := (e.find? fun x => genericBinderHeads.any x.isConstOf).isSome
  return hit ty || hit ty'

/-- Check and fill a node or edge record of the logic graph. -/
def logicRecord (kind : String) (name? : Option String) (fs : Fields) :
    CommandElabM (Array (String × Fields)) := liftTermElabM do
  let name ← needName kind name?
  let some (head, ends?) := logicKindHead kind | throwError "silmaril: {kind} is not a logic-graph kind"
  let d ← fs.const kind "decl"
  let info ← getConstInfo d
  if info matches .thmInfo _ then
    throwError "silmaril {kind}: {d} is a theorem; register the definition"
  let given (k : String) := match fs.get? k with | some (.str s) => some s | _ => none
  -- one node per institution or room: a definition identical to a registered one's is a duplicate
  if kind == "institution" || kind == "room" then
    if let some v := info.value? then
      for r in records (← getEnv) do
        unless r.kind == kind do continue
        let some d' := r.str? "decl" | continue
        let some i' := (← getEnv).find? d'.toName | continue
        let some v' := i'.value? | continue
        if i'.levelParams.length == info.levelParams.length &&
            v' == v.instantiateLevelParams info.levelParams (i'.levelParams.map Level.param) then
          throwError "silmaril {kind}: {d} is defined exactly as {d'}, registered as {kind} {r.name}: \
            the same {kind} is registered once"
  let filled ← logicTelescope d fun xs ty => do
    unless ty.isAppOf head do
      throwError "silmaril {kind}: {d} has type{indentExpr info.type}\nbut a {kind} is a `{head}` \
        (or a family of them)"
    for x in xs do
      if ← genericBinder (← inferType x) then
        throwError "silmaril {kind}: {d} is a generic construction: its binder \
          `{(← x.fvarId!.getDecl).userName}` ranges over institutions, rooms or maps, so it is not \
          a node or an edge of the graph (the audit lists it as generic)"
    let mut out : Array (String × Json) := #[("arity", toJson xs.size)]
    unless xs.isEmpty do out := out.push ("params", .str (← paramsOf xs))
    if let some ofKind := ends? then
      let args := ty.getAppArgs
      let (a, b) := (args[args.size - 2]!, args[args.size - 1]!)
      let (src, srcAt) ← resolveEndpoint kind "from" ofKind a (given "from")
      let (tgt, tgtAt) ← resolveEndpoint kind "to" ofKind b (given "to")
      out := out ++ #[("from", .str src), ("to", .str tgt)]
      unless srcAt.isEmpty do out := out.push ("from_at", .str (" ".intercalate srcAt.toList))
      unless tgtAt.isEmpty do out := out.push ("to_at", .str (" ".intercalate tgtAt.toList))
    if kind == "room" then
      let R := mkAppN (mkConst d (info.levelParams.map Level.param)) xs
      let (sen, mod) ← roomTypes R
      out := out ++ #[("sen", .str (← ppOneLine sen)), ("mod", .str (← ppOneLine mod))]
      if let some (i, s) ← roomInstitution? R (given "institution") then
        out := out ++ #[("institution", .str i), ("signature", .str s)]
    return out
  let mut fs := ((fs.erase "from").erase "to").erase "institution"
  for (k, v) in filled do fs ← fs.push kind k v
  fs ← fs.push kind "type" (.str (← ppLogic info.type))
  fs ← fs.push kind "levels" (.str (← levelsOf d))
  if (fs.get? "doc").isNone then
    if let some doc ← findDocString? (← getEnv) d then
      fs ← fs.push kind "doc" (.str doc.trimAscii.toString)
  if let some facts ← checkFacts kind d fs then
    fs := fs.set "facts" facts
  match fs.get? "hets", fs.get? "hets_relation" with
  | some _, none => throwError "silmaril {kind}: `hets` needs `(hets_relation := corresponds | fragment | related)`"
  | none, some _ => throwError "silmaril {kind}: `hets_relation` needs `hets`"
  | _, _ => pure ()
  return #[(name, fs)]

@[silmaril_kind institution] def institutionHandler : Handler where
  run? := some logicRecord
@[silmaril_kind comorphism] def comorphismHandler : Handler where
  run? := some logicRecord
@[silmaril_kind morphism] def morphismHandler : Handler where
  run? := some logicRecord
@[silmaril_kind corridor] def corridorHandler : Handler where
  run? := some logicRecord
/-- Rooms are logic-graph nodes too: this handler replaces `Registry.Room.Defs`'s. -/
@[silmaril_kind room] def roomGraphHandler : Handler where
  run? := some logicRecord

/-! ## The audit -/

/-- A record name for a declaration: `audit.` and its components, lower case, each character
outside `[a-z0-9_-]` written as `-u<hex>`, a segment not starting with a letter prefixed by `x`. -/
def auditName (d : Name) : String :=
  let seg (s : String) : String :=
    let body := String.join (s.toList.map fun c =>
      if c.isLower || c.isDigit || c == '_' || c == '-' then c.toString
      else if c.isUpper then c.toLower.toString
      else s!"-u{String.ofList (Nat.toDigits 16 c.toNat)}")
    if body.front.isLower then body else "x" ++ body
  "audit." ++ ".".intercalate (d.components.map fun c => seg (c.toString (escape := false)))

/-- The layer of a module: `proofs`, `raw` or `header`. -/
def moduleLayer (m : Name) : String :=
  match m.components with
  | _ :: `Proofs :: _ => "proofs"
  | _ :: `Raw :: _ => "raw"
  | _ => "header"

/-- `logic_audit (prefix := P)`: one record per declaration under `P` of a logic-graph type. -/
@[silmaril_kind logic_audit] def logicAuditHandler : Handler where
  run? := some fun kind _ fs => liftTermElabM do
    let some (.str pre) := fs.get? "prefix" | throwError "silmaril {kind}: `(prefix := \"P\")` is required"
    let pre := pre.toName
    let env ← getEnv
    -- registered declarations, by kind
    let mut reg : Std.HashMap Name (String × String) := {}
    for r in records env do
      if (logicKindHead r.kind).isSome then
        if let some d := r.str? "decl" then reg := reg.insert d.toName (r.kind, r.name)
    let mut found : Array (Name × String × Nat × Bool × Name) := #[]
    for (n, info) in env.constants.toList do
      unless pre.isPrefixOf n do continue
      if n.isInternalDetail || isPrivateName n then continue
      if info matches .thmInfo _ || info matches .ctorInfo _ || info matches .recInfo _ then continue
      if info matches .inductInfo _ then continue
      if isAuxRecursor env n || isNoConfusion env n then continue
      let some m := env.getModuleIdxFor? n | continue
      -- deep types (large inductive signatures) get a higher recursion limit; a type that still
      -- cannot be unfolded is not classified (not a node or an edge of a known kind)
      let r? ← tryCatchRuntimeEx (withTheReader Core.Context (fun c => { c with maxRecDepth := 8192 }) <|
          forallTelescopeReducing info.type fun xs body => do
            let body ← whnfR body
            let some k := body.getAppFn.constName?.bind logicKindOf? | return none
            let g ← xs.anyM fun x => do genericBinder (← inferType x)
            return some (k, xs.size, g))
        fun _ => pure none
      if let some (k, arity, g) := r? then
        found := found.push (n, k, arity, g, env.header.moduleNames[m.toNat]!)
    found := found.qsort fun a b => a.1.toString < b.1.toString
    let mut out := #[]
    let mut used : Std.HashSet String := {}
    for (n, k, arity, g, m) in found do
      let mut nm := auditName n
      if used.contains nm then
        let mut i := 2
        while used.contains s!"{nm}-{i}" do i := i + 1
        nm := s!"{nm}-{i}"
      used := used.insert nm
      let mut f : Fields := {}
      f ← f.push kind "decl" (.str n.toString)
      f ← f.push kind "object" (.str k)
      f ← f.push kind "arity" (toJson arity)
      f ← f.push kind "generic" (toJson g)
      f ← f.push kind "decl_module" (.str m.toString)
      f ← f.push kind "layer" (.str (moduleLayer m))
      f ← f.push kind "scope" (.str pre.toString)
      if let some (rk, rn) := reg.get? n then
        unless rk == k do
          throwError "silmaril {kind}: {n} is registered as a {rk} but its type is a {k}"
        f ← f.push kind "registered" (.str rn)
      out := out.push (nm, f)
    return out

/-! ## The curated catalogue

`silmaril logic_catalogue N (catalogue_id := …) (entry := node | edge) (status := …)
(records := ["kind:name", …]) (evidence := [decl, …]) (reason := …)` records what one entry of
the curated catalogue the logic-graph port started from is in this repository. Lean checks that
every evidence declaration exists (the entry's Lean code is here) and that every record it names
is registered; `sil project check` checks the status against the records and the reason. -/

/-- The statuses of a catalogue entry. -/
def catalogueStatuses : List String :=
  ["registered", "represented", "not-institution-typed", "prospective"]

@[silmaril_kind logic_catalogue] def logicCatalogueHandler : Handler where
  run? := some fun kind name? fs => liftTermElabM do
    let name ← needName kind name?
    let env ← getEnv
    let some (.str status) := fs.get? "status" | throwError "silmaril {kind}: `status` is required"
    unless catalogueStatuses.contains status do
      throwError "silmaril {kind}: status {status.quote} is not one of {catalogueStatuses}"
    if let some (.arr es) := fs.get? "evidence" then
      for e in es do
        let .str d := e | throwError "silmaril {kind}: `evidence` is a list of declarations"
        unless env.contains d.toName do
          throwError "silmaril {kind}: evidence {d} is not a declaration of the environment"
    if let some (.arr rs) := fs.get? "records" then
      for r in rs do
        let .str s := r | throwError "silmaril {kind}: `records` is a list of `kind:name`"
        match s.splitOn ":" with
        | [k, n] =>
          unless (logicKindHead k).isSome do throwError "silmaril {kind}: {k} is not a logic-graph kind"
          unless (findRecord? env k n).isSome do throwError "silmaril {kind}: no {k} {n} is registered"
        | _ => throwError "silmaril {kind}: record {s.quote} is not `kind:name`"
    return #[(name, fs)]

end Silmaril.Project
