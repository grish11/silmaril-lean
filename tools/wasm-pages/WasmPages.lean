import Lean.Data.Json
import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Tools.Text.Defs
import Silmaril.Wasm.Tools.Validate.Defs
import Silmaril.Wasm.Tools.Features.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Print.Defs
import Silmaril.Wasm.Component.Binary.Defs
import Silmaril.Wasm.Component.Binary.Encode.Defs
import Silmaril.Wasm.Wit.Tool.Defs
import Silmaril.Wasm.Cfg.BlockCfg.Defs
import Silmaril.Wasm.Cfg.Examples.Defs
import Silmaril.Wasm.Binaryen.Exe.Encode
import Silmaril.Wasm.Tools.Meta.Demangle.Defs
import Silmaril.Wasm.Wit.Binary.Embed.Defs
import Silmaril.Wasm.Tools.CompValidate.Defs
import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Wasm.Cfg.BlockTyping.Defs
import Silmaril.Wasm.Cfg.Variant.Defs
import Silmaril.Wasm.Cfg.Maximal.Defs
import Silmaril.Crypto.SHA256
import Silmaril.Wasi.Component.Accept.Catalog.Defs

/-!
# `wasm-pages`: the data of the explorer's Wasm component, module and function pages

```
wasm-pages ARTIFACTS.toml OUTDIR
```

It reads the Wasm blobs that `ARTIFACTS.toml` registers (`meta.wasm.layer` is `module` or
`component`), plus a few example modules that are Lean values, and writes static files under
`OUTDIR/wasm/`. The explorer (`sil project explore`) reads these files.

- `index.json` lists the components and modules.
- `c/ID.json` holds a component: imports, exports, core modules, nested components and
  instances, its WAT, and WIT when the bytes are a WIT package.
- `m/ID.json` holds a module: imports, exports, functions, the call graph, and for each
  defined function its WAT and its basic-block CFG.
- `blob/ID.wasm` and `wat/ID.wat` are the downloadable bytes and text.

Each fact records where it comes from, and this file adds no semantics:
- The decoders, the printers and the validator are the library's.
- The block CFG is `Silmaril.Wasm.Cfg.blockCfg`, which is proved to compute the declarative
  relation `Edge`. That relation is syntactic and incomplete; see its module doc.
- The call graph is read off the instructions here. It is syntactic: direct calls name their
  callee, while `call_indirect` and `call_ref` go to explicit "unknown callee" nodes.
-/

open Lean (Json)
open Silmaril.Wasm

namespace WasmPages

/-! ## Small helpers -/

def jstr (s : String) : Json := Json.str s
def jnat (n : Nat) : Json := Json.num (Lean.JsonNumber.fromNat n)
def jarr (xs : List Json) : Json := Json.arr xs.toArray
def jobj (kvs : List (String × Json)) : Json := Json.mkObj kvs

/-- A file-name-safe slug of an identifier. -/
def slug (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isAlphanum || c == '.' || c == '_' || c == '-' then c else '~')

/-- Read an unsigned LEB128 at `i`. -/
partial def leb (b : ByteArray) (i : Nat) (shift acc : Nat := 0) : Option (Nat × Nat) :=
  if h : i < b.size then
    let x := b[i].toNat
    let acc := acc + (x % 128) * 2 ^ shift
    if x < 128 then some (acc, i + 1) else leb b (i + 1) (shift + 7) acc
  else none

def str (b : ByteArray) (i : Nat) : Option (String × Nat) := do
  let (n, j) ← leb b i
  if j + n ≤ b.size then
    match String.fromUTF8? (b.extract j (j + n)) with
    | some s => some (s, j + n)
    | none => none
  else none

/-- The function names of a module's `name` custom section (subsection 1), if any. -/
partial def funcNames (b : ByteArray) : List (Nat × String) := Id.run do
  let mut i := 8
  let mut out : List (Nat × String) := []
  while i < b.size do
    let id := b[i]!.toNat
    match leb b (i + 1) with
    | none => return out
    | some (size, j) =>
      let next := j + size
      if id == 0 then
        if let some (nm, k) := str b j then
          if nm == "name" then
            let mut p := k
            while p < next do
              let sid := b[p]!.toNat
              match leb b (p + 1) with
              | none => p := next
              | some (ssize, q) =>
                if sid == 1 then
                  if let some (cnt, r) := leb b q then
                    let mut r := r
                    for _ in [0:cnt] do
                      match leb b r with
                      | none => break
                      | some (fi, r1) =>
                        match str b r1 with
                        | none => break
                        | some (fname, r2) => out := (fi, fname) :: out; r := r2
                p := q + ssize
      i := next
  return out.reverse

/-- A name as `wasm-tools demangle` shows it (Rust v0/legacy, Itanium C++), when it changes. -/
def demangled (s : String) : Option String :=
  let d := Silmaril.Wasm.Tools.Meta.Demangle.demangleName s.toUTF8.data.toList
  match String.fromUTF8? (ByteArray.mk d.toArray) with
  | some t => if t != s then some t else none
  | none => none

def nameFields (n : Option String) : List (String × Json) :=
  [("name", match n with | some x => jstr x | none => Json.null),
   ("display", match n.bind demangled with | some x => jstr x | none => Json.null)]

/-! ## Instructions -/

open Silmaril.Wasm.Tools.Gen.Cmd.Print in
/-- The text of one instruction: the printer's, else the CFG's mnemonic. -/
def instrText (i : Instr) : String := (plain 0 i).getD (Cfg.mnemonic i)

/-- Every instruction of a body, nested ones included. -/
partial def allInstrs : List Instr → List Instr
  | [] => []
  | i :: is =>
    let inner := match i with
      | .block _ b | .loop _ b | .tryTable _ _ b => allInstrs b
      | .if_ _ t e => allInstrs t ++ allInstrs e
      | _ => []
    i :: (inner ++ allInstrs is)

/-- A call site: the callee (`some` function index for direct calls) and its kind. -/
def callOf : Instr → Option (Option Nat × String × String)
  | .call f => some (some f.value.val, "direct", "")
  | .returnCall f => some (some f.value.val, "tail", "")
  | .callIndirect t ty => some (none, "indirect", s!"table {t.value.val}, type {ty.value.val}")
  | .returnCallIndirect t ty => some (none, "indirect-tail", s!"table {t.value.val}, type {ty.value.val}")
  | .callRef ty => some (none, "ref", s!"type {ty.value.val}")
  | .returnCallRef ty => some (none, "ref-tail", s!"type {ty.value.val}")
  | _ => none

/-! ## Types -/

open Silmaril.Wasm.Tools.Gen.Cmd.Print in
def vt (t : ValType) : String := (valType t).getD "ref"

def funcTypeOf (m : Module) (ty : Nat) : Option FuncType :=
  match m.typeDefinitions[ty]? with
  | some ⟨_, _, .func ft⟩ => some ft
  | _ => none

def sigText (m : Module) (ty : Nat) : String :=
  match funcTypeOf m ty with
  | some ft =>
    let ps := if ft.params.isEmpty then "" else " (param " ++ " ".intercalate (ft.params.map vt) ++ ")"
    let rs := if ft.results.isEmpty then "" else " (result " ++ " ".intercalate (ft.results.map vt) ++ ")"
    s!"(type {ty}){ps}{rs}"
  | none => s!"(type {ty})"

def externKind : ExternType → String
  | .func _ => "func" | .table _ => "table" | .memory _ => "memory"
  | .global _ => "global" | .tag _ => "tag"

def exportKind : ExternIdx → String × Nat
  | .func i => ("func", i.value.val) | .table i => ("table", i.value.val)
  | .memory i => ("memory", i.value.val) | .global i => ("global", i.value.val)
  | .tag i => ("tag", i.value.val)

/-! ## Block typing, from the validator's instruction checker

The stack at each block's entry and before its terminator, computed by running the validator's
instruction checker (`Validation.CheckInstrs.checkInstr`, which `checkModule?` uses) along the
body. These are runtime results of the checker, not a typing theorem about the block. -/

namespace Typing
open Silmaril.Wasm.Validation

def heapText : Ty .heap → String
  | .abs a => Silmaril.Wasm.Tools.Gen.Cmd.Print.absHeap (match a with | x => x)
  | .bot => "none"
  | .use _ => "$type"

def cvt : Ty .val → String
  | .num (.int .i32) => "i32" | .num (.int .i64) => "i64"
  | .num (.float .f32) => "f32" | .num (.float .f64) => "f64"
  | .vec _ => "v128"
  | .refv (.ref n h) => (if n then "(ref null " else "(ref ") ++ heapText h ++ ")"
  | .botv => "⊥"

def stackText (s : List (Ty .val)) : String := "[" ++ " ".intercalate (s.map cvt) ++ "]"

/-- The module's validation context (`checkModule?`'s `C`), if the module validates that far. -/
def moduleContext? (m : Module) : Option Context := do
  let K := defaultCheckers
  let dts ← K.types? {} m.types
  let xtI ← m.imports.mapM (K.import? { types := dts })
  let fdts ← m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type)
  let C' := moduleCtx' m dts xtI fdts
  let jts ← m.tags.mapM (K.tag? C')
  let gts ← K.globals? C' m.globals
  let tts ← m.tables.mapM (K.table? C')
  let rts := m.elems.map fun e => C'.closeRef e.type
  pure (moduleCtx m C' xtI jts gts tts rts)

/-- The context of a function body, and its parameter and result types. -/
def funcContext? (C : Context) (f : Func) : Option (Context × List (Ty .val)) := do
  let d ← C.type? f.type
  match d.expand? with
  | some (.func ps rs) =>
    let lts ← localsCheck? tyOkC C f.locals
    pure (C.funcBody ps.toList rs.toList lts, rs.toList)
  | _ => none

def labelText (C : Context) (l : LabelIdx) : String :=
  match C.labels[l.value.val]? with
  | some ts => s!"label {l.value.val}: {stackText ts}"
  | none => s!"label {l.value.val}: none"

/-- Branch targets' label types, for a terminator. -/
def branchText (C : Context) : Instr → Option String
  | .br l | .brIf l | .brOnNull l | .brOnNonNull l | .brOnCast l .. | .brOnCastFail l .. => some (labelText C l)
  | .brTable ls d => some ("; ".intercalate ((ls ++ [d]).map (labelText C)))
  | .return_ => some (match C.return_ with | some ts => s!"return {stackText ts}" | none => "return")
  | _ => none

/-- Per block `(path, position)`: its interface from `Cfg.bodyIfaces` (each one proved an
`Instrs_ok` derivation, `bodyIfaces_typed`), shown when its instructions are the block's own. -/
def ifaceJson (segOf : Cfg.BlockId → Option (List Instr)) (x : Cfg.BlockIface) : Option Json :=
  if (segOf x.id).map (fun l => reprStr l) == some (reprStr x.instrs) then
    let inS := List.replicate x.pad Ty.botv ++ x.inStk
    let br := match x.instrs.getLast? with
      | some t => if Cfg.isTerminator t then (branchText x.ctx t).getD "" else ""
      | none => ""
    some (jobj [("in", jstr (stackText inS)), ("out", jstr (stackText x.outStk)),
      ("inits", jarr (x.inits.map jnat)), ("labels", jstr (" ".intercalate (x.ctx.labels.map stackText))),
      ("branch", jstr br)])
  else none

end Typing

/-! ## The block CFG of a function -/

def targetJson (ids : List Cfg.BlockId) : Cfg.Target → Json
  | .block b => jnat (ids.idxOf b)
  | .exit => jstr "exit" | .trap => jstr "trap" | .raise => jstr "raise" | .invalid => jstr "invalid"

/-- The indices one instruction names: `(space, index)`, syntactically (nested bodies excluded). -/
def instrRefs : Instr → List (String × Nat)
  | .localGet i | .localSet i | .localTee i => [("local", i.value.val)]
  | .globalGet i | .globalSet i => [("global", i.value.val)]
  | .call f | .returnCall f | .refFunc f => [("func", f.value.val)]
  | .callIndirect t _ | .returnCallIndirect t _ | .tableGet t | .tableSet t | .tableSize t
  | .tableGrow t | .tableFill t | .tableInit t _ => [("table", t.value.val)]
  | .throw t => [("tag", t.value.val)]
  | _ => []

/-- A block's referenced indices, by space, without repetition. -/
def refsJson (is : List Instr) : Json :=
  let rs := (is.flatMap instrRefs).eraseDups
  jobj (["local", "global", "func", "table", "tag"].filterMap fun sp =>
    let xs := (rs.filter (·.1 == sp)).map (·.2)
    if xs.isEmpty then none else some (sp, jarr (xs.map jnat)))

def effectName : Cfg.Effect → String
  | .mayTrap => "may-trap" | .call => "call" | .unresolvedHandler => "handler-unresolved"

/-- A handler for the all-effects outcomes: a node index, `"caller"`, or `"unresolved"`. -/
def handlerJson (node : Cfg.BlockId → Option Nat) : Cfg.Target → Json
  | .block b => match node b with | some n => jnat n | none => jstr "unresolved"
  | .raise => jstr "caller"
  | _ => jstr "unresolved"

/-- The all-effects outcomes of a block's instructions `is` (with terminator `term`) at `node`. -/
def aeOutcomes (body : Expr) (b : Cfg.BlockId) (instrNode : Nat → Nat) (blockNode : Cfg.BlockId → Option Nat)
    (s : Cfg.Segment) : List Json × List Json :=
  let hs := Cfg.raiseHandlers body b.seq
  let raiseOf (n : Nat) (eff : String) : List Json × List Json :=
    (hs.map fun h => jarr [jnat n, jstr eff, handlerJson blockNode h],
     hs.filterMap fun h => match h with
       | .block hb => (blockNode hb).map fun t => jarr [jnat n, jnat t, jstr "handler"]
       | _ => none)
  let perInstr := s.body.zipIdx.map fun (i, k) =>
    let es := Cfg.instrEffects i
    let trap := if es.contains .mayTrap || es.contains .call then [jarr [jnat (instrNode k), jstr "may-trap"]] else []
    let (ro, re) := if es.contains .call then raiseOf (instrNode k) "may-raise" else ([], [])
    (trap ++ ro, re)
  let termPart : List Json × List Json := match s.term with
    | some t =>
      let n := instrNode s.body.length
      let es := Cfg.instrEffects t
      let base := if es.contains .mayTrap || es.contains .call then [jarr [jnat n, jstr "may-trap"]] else []
      let (cr, ce) := if es.contains .call then raiseOf n "may-raise" else ([], [])
      match t with
      | .unreachable => ([jarr [jnat n, jstr "trap"]], [])
      | .throw _ | .throwRef => let (o, e) := raiseOf n "raise"; (base ++ o, e)
      | _ => (base ++ cr, ce)
    | none => ([], [])
  ((perInstr.flatMap (·.1)) ++ termPart.1, (perInstr.flatMap (·.2)) ++ termPart.2)

def cfgJson (body : Expr) (typing : List ((List Cfg.SeqStep × Nat) × Json) := [])
    (kernelTable : Option String := none) : Json :=
  let bs := Cfg.blocks body
  let ids := bs.map (·.1)
  let flow := Cfg.blockCfg body
  let blocksJ := bs.map fun (b, s) => jobj [
    ("path", jstr (".".intercalate (b.seq.map fun (m, a) => s!"{m}/{a}"))),
    ("pos", jnat b.idx),
    ("instrs", jarr (s.body.map (jstr ∘ instrText))),
    ("term", match s.term with | some t => jstr (instrText t) | none => Json.null),
    ("effects", jarr ((Cfg.blockEffects body b s).map (jstr ∘ effectName))),
    ("refs", refsJson s.instrs),
    ("typing", match typing.lookup (b.seq, b.idx) with | some j => j | none => Json.null)]
  let flowJ := flow.flatMap fun (b, ts) =>
    ts.map fun t => jarr [jnat (ids.idxOf b), targetJson ids t, jstr "flow"]
  let effJ := bs.flatMap fun (b, s) =>
    (Cfg.effectSucc body b s).map fun t => jarr [jnat (ids.idxOf b), targetJson ids t, jstr "effect"]
  let blockNode (b : Cfg.BlockId) : Option Nat := if ids.contains b then some (ids.idxOf b) else none
  -- all-effects, block level: flow edges to neither sink; outcomes and handler edges
  let aeFlow := bs.flatMap fun (b, s) =>
    (Cfg.succAE body b s).map fun t => jarr [jnat (ids.idxOf b), targetJson ids t, jstr "flow"]
  let aeParts := bs.map fun (b, s) => aeOutcomes body b (fun _ => ids.idxOf b) blockNode s
  let aeOut := (aeParts.flatMap (·.1)).eraseDups
  let aeHandler := (aeParts.flatMap (·.2)).eraseDups
  let aeBases := jarr [
    jobj [("id", jstr "flow"), ("kinds", jarr [jstr "flow"]), ("relation", jstr "Silmaril.Wasm.Cfg.EdgeAE")],
    jobj [("id", jstr "flow+handler"), ("kinds", jarr [jstr "flow", jstr "handler"]),
      ("relation", jstr "Silmaril.Wasm.Cfg.EdgeAE ∪ handler edges from Silmaril.Wasm.Cfg.raiseHandlers")]]
  let aeBlock := jobj [("model", jstr "all-effects"), ("granularity", jstr "block"),
    ("entry", targetJson ids (Cfg.cfgEntry body)), ("edges", jarr (aeFlow ++ aeHandler)),
    ("outcomes", jarr aeOut), ("bases", aeBases),
    ("relation", jstr "Silmaril.Wasm.Cfg.edge_iff_ae")]
  -- all-effects, instruction level: node k = [block, position]; position = instrs.length is the terminator
  let nodeLists := bs.map fun (_, s) => s.body.length + (if s.term.isSome then 1 else 0)
  let offsets := (nodeLists.foldl (fun (acc : List Nat × Nat) n => (acc.1 ++ [acc.2], acc.2 + n)) ([], 0)).1
  let nodesJ := (bs.zipIdx.flatMap fun ((_, _), n) =>
    (List.range (nodeLists.getD n 0)).map fun p => jarr [jnat n, jnat p])
  let firstNode (n : Nat) := offsets.getD n 0
  let lastNode (n : Nat) := offsets.getD n 0 + nodeLists.getD n 1 - 1
  let instrTarget : Cfg.Target → Json
    | .block b => match blockNode b with | some n => jnat (firstNode n) | none => jstr "invalid"
    | t => targetJson ids t
  let seqEdges := bs.zipIdx.flatMap fun (_, n) =>
    (List.range (nodeLists.getD n 0 - 1)).map fun p => jarr [jnat (firstNode n + p), jnat (firstNode n + p + 1), jstr "flow"]
  let outEdges := bs.flatMap fun (b, s) =>
    let n := ids.idxOf b
    (Cfg.succAE body b s).map fun t => jarr [jnat (lastNode n), instrTarget t, jstr "flow"]
  let instrParts := bs.zipIdx.map fun ((b, s), n) =>
    aeOutcomes body b (fun k => firstNode n + k) (fun hb => (blockNode hb).map firstNode) s
  let aeInstr := jobj [("model", jstr "all-effects"), ("granularity", jstr "instr"), ("nodes", jarr nodesJ),
    ("entry", instrTarget (Cfg.cfgEntry body)), ("edges", jarr (seqEdges ++ outEdges ++ (instrParts.flatMap (·.2)).eraseDups)),
    ("outcomes", jarr (instrParts.flatMap (·.1)).eraseDups), ("bases", aeBases),
    ("relation", jstr "Silmaril.Wasm.Cfg.EdgeAE refined to instructions by wasm-pages (no separate theorem)")]
  let legacyBases := jarr ([
    jobj [("id", jstr "flow"), ("kinds", jarr [jstr "flow"]), ("relation", jstr "Silmaril.Wasm.Cfg.Edge")],
    jobj ([("id", jstr "flow+effect"), ("kinds", jarr [jstr "flow", jstr "effect"]),
      ("relation", jstr "Silmaril.Wasm.Cfg.Edge ∪ Silmaril.Wasm.Cfg.EffectEdge")] ++
      (match kernelTable with | some k => [("kernelTable", jstr k)] | none => []))])
  -- maximal blocks: chains of `Cfg.canMerge` (functional and injective: `canMerge_functional`,
  -- `canMerge_inj`), starting at the blocks no merge reaches. The edges are exactly `Cfg.maxFlow`
  -- (AE edges that are not merged fall-throughs, `mem_maxFlow`) and `Cfg.maxHandler`
  -- (`mem_maxHandler`), mapped to their maximal blocks; nothing else is dropped, so a loop back
  -- into its own maximal block stays an edge. Outcomes stay per member, in member order.
  -- The grouping is `Cfg.maxGroups`, accepted by the checker `Cfg.groupsOk` (`groupsOk_sound`:
  -- every block in exactly one group, each group a maximal merge chain). If the checker rejects
  -- it, no maximal graph is published.
  let groupsB := Cfg.maxGroups body
  let maxOk := Cfg.groupsOk body groupsB
  let groups := groupsB.map (·.map ids.idxOf)
  let groupOf (i : Nat) : Nat := (groups.findIdx? (·.contains i)).getD i
  let gOfBlock (b : Cfg.BlockId) : Option Nat := (blockNode b).map groupOf
  let gTargetJ : Cfg.Target → Json
    | .block c => match gOfBlock c with | some g => jnat g | none => jstr "invalid"
    | t => targetJson ids t
  let maxFlowJ := (Cfg.maxFlow body).map fun (b, t) => jarr [jnat (groupOf (ids.idxOf b)), gTargetJ t, jstr "flow"]
  let maxHandlerJ := (Cfg.maxHandler body).filterMap fun (b, t) => match t with
    | .block c => (gOfBlock c).map fun g => jarr [jnat (groupOf (ids.idxOf b)), jnat g, jstr "handler"]
    | _ => none
  let maxOutcomes := groups.zipIdx.flatMap fun (ms, g) => ms.flatMap fun m =>
    ((aeParts.getD m ([], [])).1.eraseDups).map fun o => match o with
      | .arr xs => match xs.toList with
        | _ :: eff :: rest =>
          let h := match rest.head? with
            | some (.num n) => match n.mantissa.toNat? with | some k => jnat (groupOf k) | none => Json.null
            | some j => j
            | none => Json.null
          jarr [jnat g, eff, h, jnat m]
        | _ => o
      | _ => o
  let gBlocks := groups.map fun ms =>
    let mem := ms.filterMap fun i => bs[i]?
    let instrs := mem.zipIdx.flatMap fun ((_, s), k) =>
      s.body.map (jstr ∘ instrText) ++
        (if k + 1 < mem.length then (s.term.map (jstr ∘ instrText)).toList else [])
    let hb : Cfg.BlockId := match mem.head? with | some (b, _) => b | none => ⟨[], 0⟩
    jobj [("path", jstr (".".intercalate (hb.seq.map fun (m, a) => s!"{m}/{a}"))), ("pos", jnat hb.idx),
      ("instrs", jarr instrs),
      ("term", match mem.getLast? with | some (_, s) => (match s.term with | some t => jstr (instrText t) | none => Json.null) | none => Json.null),
      ("effects", jarr ((mem.flatMap fun (b, s) => Cfg.blockEffects body b s).eraseDups.map (jstr ∘ effectName))),
      -- Typing stays per member: entering a `block`/`loop`/`if`/`try_table` between members changes
      -- the label context, so the members' instructions are not one instruction sequence.
      ("typing", Json.null),
      ("memberTyping", jarr (mem.map fun (b, _) => match typing.lookup (b.seq, b.idx) with | some j => j | none => Json.null)),
      ("members", jarr (ms.map jnat))]
  let maxEdges := (maxFlowJ ++ maxHandlerJ).eraseDups
  let maxBlock := jobj [("model", jstr "all-effects"), ("granularity", jstr "block"),
    ("blocks", jarr gBlocks), ("members", jarr (groups.map fun ms => jarr (ms.map jnat))),
    ("entry", gTargetJ (Cfg.cfgEntry body)), ("edges", jarr maxEdges),
    ("outcomes", jarr maxOutcomes), ("bases", aeBases),
    ("note", jstr "Outcomes are [maximal block, effect, handler or null, member block]: each member keeps its own outcomes, in member order."),
    ("relation", jstr ("Silmaril.Wasm.Cfg.mem_maxFlow, mem_maxHandler (the kept edges, by member); " ++
      "canMerge_functional, canMerge_inj, canMerge_not_entry (merges form disjoint chains); " ++
      "maxGroups accepted by groupsOk (groupsOk_sound, groupOk_spec: every block in exactly one maximal merge chain)"))]
  let maxVariants := if maxOk then [("all-effects-max", maxBlock)] else []
  jobj [("model", jstr "explicit-sink"), ("entry", targetJson ids (Cfg.cfgEntry body)), ("blocks", jarr blocksJ),
        ("edges", jarr (flowJ ++ effJ)), ("bases", legacyBases),
        ("variants", jobj (maxVariants ++ [("all-effects", aeBlock), ("all-effects-instr", aeInstr)])),
        ("default", jstr (if maxOk then "all-effects-max" else "all-effects"))]

/-- The block CFGs whose dominator table is Lean kernel-checked (machine documents loaded by
`examples/project/ProjectSelfTest/WasmBlockCfg.lean`, over flow and effect edges). -/
def kernelTables : List (String × String) := [
  ("silmaril.wasm.examples.verified.prog/3", "silmaril.wasm.blockcfg.verified.sum"),
  ("silmaril.wasm.cfg.examples.mod/0", "silmaril.wasm.blockcfg.dispatch"),
  ("silmaril.wasm.cfg.examples.mod/1", "silmaril.wasm.blockcfg.specials"),
  ("silmaril.wasm.cfg.examples.effects/1", "silmaril.wasm.blockcfg.guarded"),
  ("silmaril.wasm.examples.rust_door/5", "silmaril.wasm.blockcfg.rust_door.enter")]

/-! ## Modules -/

open Silmaril.Wasm.Tools.Gen.Cmd.Print in
/-- The WAT of one defined function, printed from the decoded AST. -/
def funcWat (m : Module) (idx : Nat) (name : Option String) (f : Func) : String :=
  let nm := match name with | some n => s!" ${n}" | none => ""
  let locals := if f.locals.isEmpty then [] else ["  (local " ++ " ".intercalate (f.locals.map vt) ++ ")"]
  match bodyLines 0 f.body with
  | some ls => "\n".intercalate ([s!"(func{nm} (;{idx};) {sigText m f.type.value.val}"] ++ locals ++
      ls.map (fun l => "  " ++ String.ofList (l.toList.dropWhile (· == ' '))) ++ [")"])
  | none => s!"(func{nm} (;{idx};) {sigText m f.type.value.val}\n  ;; this printer does not print some instruction of this body\n)"

/-- Where a module or component comes from. -/
structure Source where
  kind : String           -- "artifact", "embedded", "lean"
  name : String
  cid : Option String := none
  sha256 : Option String := none
  path : Option String := none
  parent : Option String := none
  doc : String := ""

def sourceJson (s : Source) : Json := jobj [
  ("kind", jstr s.kind), ("name", jstr s.name),
  ("cid", match s.cid with | some c => jstr c | none => Json.null),
  ("sha256", match s.sha256 with | some c => jstr c | none => Json.null),
  ("path", match s.path with | some c => jstr c | none => Json.null),
  ("parent", match s.parent with | some c => jstr c | none => Json.null),
  ("doc", jstr s.doc)]

/-- The output of one processed item, accumulated. -/
structure Out where
  modules : Array Json := #[]
  functions : Array Json := #[]
  components : Array Json := #[]
  files : Array (String × ByteArray) := #[]

abbrev M := StateT Out IO

def writeFile (rel : String) (b : ByteArray) : M Unit :=
  modify fun o => { o with files := o.files.push (rel, b) }

def writeText (rel : String) (s : String) : M Unit := writeFile rel s.toUTF8

def validity (bytes : Option ByteArray) : Json :=
  match bytes with
  | none => jobj [("status", jstr "unchecked"), ("note", jstr "no bytes")]
  | some b =>
    match Silmaril.Wasm.Tools.Validate.check Silmaril.Wasm.Tools.Features.WFeatures.dflt b with
    | .ok () => jobj [("status", jstr "valid"),
        ("note", jstr "Silmaril.Wasm.Tools.Validate.check with wasm-tools' default features (check_ok_iff: equal to the specification validator)")]
    | .error e => jobj [("status", jstr "rejected"), ("note", jstr (reprStr e))]

/-- Process a core module (decoded `m`, bytes if any, source WAT if any). -/
def doModule (id title : String) (src : Source) (m : Module) (bytes : Option ByteArray)
    (srcWat : Option String := none) : M Unit := do
  let sl := slug id
  let names := match bytes with | some b => funcNames b | none => []
  let imports := m.imports
  let fimports := imports.filter fun i => match i.type with | .func _ => true | _ => false
  let nImp := fimports.length
  let exportName (fi : Nat) : Option String :=
    (m.exports.find? fun e => match e.index with | .func i => i.value.val == fi | _ => false).map (·.name)
  let nameOf (fi : Nat) : Option String :=
    match names.lookup fi with | some n => some n | none => exportName fi
  let funcsJ : List Json :=
    (fimports.zipIdx.map fun (imp, k) =>
      let ty := match imp.type with | .func t => t.value.val | _ => 0
      jobj ([("idx", jnat k), ("imported", Json.bool true), ("import", jstr s!"{imp.moduleName}/{imp.name}")] ++
        nameFields (nameOf k) ++ [
        ("sig", jstr (sigText m ty))])) ++
    (m.funcs.zipIdx.map fun (f, k) =>
      let idx := nImp + k
      let bs := Cfg.blocks f.body
      let effs := (bs.flatMap fun (b, s) => Cfg.blockEffects f.body b s).eraseDups
      jobj ([("idx", jnat idx), ("imported", Json.bool false)] ++ nameFields (nameOf idx) ++ [
        ("export", match exportName idx with | some n => jstr n | none => Json.null),
        ("sig", jstr (sigText m f.type.value.val)),
        ("locals", jnat f.locals.length),
        ("instrs", jnat (allInstrs f.body).length),
        ("blocks", jnat bs.length),
        ("effects", jarr (effs.map (jstr ∘ effectName)))]))
  -- the call graph: (caller, callee or unknown node, kind, count)
  let calls : List (Nat × Json × String) := m.funcs.zipIdx.flatMap fun (f, k) =>
    (allInstrs f.body).filterMap fun i => (callOf i).map fun (tgt, kind, what) =>
      (nImp + k, (match tgt with | some t => jnat t | none => jstr s!"{kind}: {what}"), kind)
  let grouped := calls.foldl (fun (acc : List ((Nat × Json × String) × Nat)) c =>
    match acc.find? (fun (d, _) => d.1 == c.1 && d.2.1 == c.2.1 && d.2.2 == c.2.2) with
    | some _ => acc.map fun (d, n) => if d.1 == c.1 && d.2.1 == c.2.1 && d.2.2 == c.2.2 then (d, n + 1) else (d, n)
    | none => acc ++ [(c, 1)]) []
  let callsJ := grouped.map fun ((a, b, kind), n) => jarr [jnat a, b, jstr kind, jnat n]
  -- functions whose address is taken (elem segments, ref.func): candidates for indirect calls
  let refFuncs := (m.funcs.flatMap fun f => (allInstrs f.body).filterMap fun
      | .refFunc fi => some fi.value.val | _ => none).eraseDups
  let elemFuncs := (m.elems.flatMap fun e => e.init.flatMap fun ex => ex.filterMap fun
      | .refFunc fi => some fi.value.val | _ => none).eraseDups
  let mctx := Typing.moduleContext? m
  let cfgs := m.funcs.zipIdx.map fun (f, k) =>
    let idx := nImp + k
    let segOf (b : Cfg.BlockId) := (Cfg.lookup f.body b).map (·.instrs)
    let typing := match mctx.bind (Typing.funcContext? · f) with
      | some (Cf, _) => (Cfg.bodyIfaces Cf f.body).filterMap fun x =>
          (Typing.ifaceJson segOf x).map fun j => ((x.id.seq, x.id.idx), j)
      | none => []
    let kt := kernelTables.lookup s!"{sl}/{idx}"
    jobj [("idx", jnat idx), ("wat", jstr (funcWat m idx (nameOf idx) f)), ("cfg", cfgJson f.body typing kt)]
  -- files
  if let some b := bytes then writeFile s!"wasm/blob/{sl}.wasm" b
  let watNote ← match bytes with
    | some b =>
      match Silmaril.Wasm.Tools.Text.binaryToWat b with
      | .ok t => do writeText s!"wasm/wat/{sl}.wat" t; pure "printed by wasm-tools print in Lean (Silmaril.Wasm.Tools.Text.binaryToWat; printModule_sound)"
      | .error e => pure s!"not printed: {e}"
    | none =>
      match srcWat with
      | some t => do writeText s!"wasm/wat/{sl}.wat" t; pure "the WAT source of the Lean value (wat3!)"
      | none => pure "no WAT available"
  -- the world the module embeds in a `component-type` custom section, as WIT text
  let embedded : Json := match bytes with
    | none => Json.null
    | some b => match Silmaril.Wasm.Wit.Binary.extractPayload b with
      | .error _ => Json.null
      | .ok _ => match Silmaril.Wasm.Wit.Binary.extractWorldType b with
        | .ok (p, n, w, _) =>
          jobj [("text", jstr (Silmaril.Wasm.Wit.Binary.printPackage { name := p, worlds := [(n, w)] })),
            ("note", jstr s!"world {n} of the component-type custom section (Wit.Binary.extractWorldType, as `wasm-wit extract`), printed by Wit.Binary.printPackage (printer unverified)")]
        | .error e => jobj [("text", Json.null), ("note", jstr s!"a component-type custom section this decoder does not read: {e}")]
  let summary := jobj [("id", jstr id), ("slug", jstr sl), ("title", jstr title), ("kind", jstr "module"),
    ("source", sourceJson src), ("size", match bytes with | some b => jnat b.size | none => Json.null),
    ("imports", jnat imports.length), ("exports", jnat m.exports.length),
    ("funcs", jnat (nImp + m.funcs.length)), ("defined", jnat m.funcs.length)]
  let full := jobj [("summary", summary),
    ("validity", validity bytes),
    ("hasBlob", Json.bool bytes.isSome), ("watNote", jstr watNote),
    ("imports", jarr (imports.map fun i => jobj [("module", jstr i.moduleName), ("name", jstr i.name), ("kind", jstr (externKind i.type))])),
    ("exports", jarr (m.exports.map fun e => let (k, i) := exportKind e.index; jobj [("name", jstr e.name), ("kind", jstr k), ("idx", jnat i)])),
    ("functions", jarr funcsJ), ("calls", jarr callsJ),
    ("addressTaken", jarr ((refFuncs ++ elemFuncs).eraseDups.map jnat)),
    ("bodies", jarr cfgs),
    ("start", match m.start with | some s => jnat s.value.val | none => Json.null),
    ("embeddedWorld", embedded)]
  writeText s!"wasm/m/{sl}.json" full.compress
  let fnIndex := m.funcs.zipIdx.map fun (f, k) =>
    let idx := nImp + k
    let n := nameOf idx
    jarr [jstr sl, jnat idx, match n.bind demangled with | some d => jstr d | none => match n with | some x => jstr x | none => Json.null,
      match exportName idx with | some e => jstr e | none => Json.null, jnat (Cfg.blocks f.body).length]
  modify fun o => { o with modules := o.modules.push summary, functions := o.functions ++ fnIndex.toArray }

/-! ## Components -/

open Silmaril.Wasm.Component.Binary in
def externDescText : ExternDesc → String
  | .coreModule _ => "core module" | .func _ => "func" | .value _ => "value" | .type _ => "type"
  | .component _ => "component" | .instance _ => "instance"

open Silmaril.Wasm.Component.Binary in
def sortText : ItemSort → String
  | .core _ => "core" | .func => "func" | .value => "value" | .type => "type"
  | .component => "component" | .instance => "instance"

open Silmaril.Wasm.Component in
partial def doComponent (id title : String) (src : Source) (b : ByteArray) : M Unit := do
  let sl := slug id
  writeFile s!"wasm/blob/{sl}.wasm" b
  match Binary.parse b with
  | .error e =>
    let summary := jobj [("id", jstr id), ("slug", jstr sl), ("title", jstr title), ("kind", jstr "component"),
      ("source", sourceJson src), ("size", jnat b.size)]
    writeText s!"wasm/c/{sl}.json" (jobj [("summary", summary), ("hasBlob", Json.bool true),
      ("unsupported", jstr s!"the component decoder rejected the bytes: {reprStr e}")]).compress
    modify fun o => { o with components := o.components.push summary }
  | .ok ast =>
    let secs := ast.sections
    let mut children : List Json := []
    let mut modK := 0
    let mut compK := 0
    for s in secs do
      match s with
      | .coreModule mb =>
        let cid := s!"{id}/module/{modK}"
        let csrc : Source := { kind := "embedded", name := s!"core module {modK} of {title}",
                               parent := some id,
                               doc := "a core module section of the component, decoded as a module" }
        match Binary.Core.Decode.decodeModule mb with
        | .ok m =>
          doModule cid s!"{title} › core module {modK}" csrc m (some mb)
          children := children ++ [jobj [("kind", jstr "module"), ("id", jstr cid), ("slug", jstr (slug cid)), ("index", jnat modK)]]
        | .error e =>
          children := children ++ [jobj [("kind", jstr "module"), ("id", jstr cid), ("index", jnat modK),
            ("unsupported", jstr s!"the module decoder rejected it: {e}")]]
        modK := modK + 1
      | .component c =>
        let cid := s!"{id}/component/{compK}"
        match Binary.encode c with
        | some cb =>
          let csrc : Source := { kind := "embedded", name := s!"component {compK} of {title}",
                                 parent := some id,
                                 doc := "a nested component section, re-encoded by the component encoder" }
          doComponent cid s!"{title} › component {compK}" csrc cb
          children := children ++ [jobj [("kind", jstr "component"), ("id", jstr cid), ("slug", jstr (slug cid)), ("index", jnat compK)]]
        | none =>
          children := children ++ [jobj [("kind", jstr "component"), ("id", jstr cid), ("index", jnat compK),
            ("unsupported", jstr "the component encoder could not re-encode it")]]
        compK := compK + 1
      | _ => pure ()
    let imports := secs.flatMap fun | .imports xs => xs | _ => []
    let exports := secs.flatMap fun | .exports xs => xs | _ => []
    let coreInsts := secs.flatMap fun | .coreInstances xs => xs | _ => []
    let insts := secs.flatMap fun | .instances xs => xs | _ => []
    let canons := secs.flatMap fun | .canons xs => xs | _ => []
    let customs := secs.filterMap fun | .custom n _ => some n | _ => none
    let coreInstJ := coreInsts.map fun
      | .instantiate mi args => jobj [("kind", jstr "instantiate"), ("module", jnat mi),
          ("args", jarr (args.map fun (n, i) => jarr [jstr n, jnat i]))]
      | .exports es => jobj [("kind", jstr "exports"), ("names", jarr (es.map fun (n, _) => jstr n))]
    let instJ := insts.map fun
      | .instantiate ci args => jobj [("kind", jstr "instantiate"), ("component", jnat ci),
          ("args", jarr (args.map fun (n, _) => jstr n))]
      | .exports es => jobj [("kind", jstr "exports"), ("names", jarr (es.map fun (n, _) => jstr n.name))]
    let canonJ := canons.map fun
      | .lift f _ ty => jstr s!"lift core func {f} (type {ty})"
      | .lower f _ => jstr s!"lower func {f}"
      | .resourceNew t => jstr s!"resource.new {t}" | .resourceDrop t => jstr s!"resource.drop {t}"
      | .resourceRep t => jstr s!"resource.rep {t}"
    let watNote ← match Silmaril.Wasm.Wit.Tool.printWat b with
      | .ok t => do writeText s!"wasm/wat/{sl}.wat" t; pure "printed by the component WAT printer (Silmaril.Wasm.Component.Wat.print)"
      | .error e => pure s!"not printed: {e}"
    let wit := match Silmaril.Wasm.Wit.Tool.witText b with
      | .ok t => jobj [("text", jstr t), ("note", jstr "Silmaril.Wasm.Wit.Tool.witText: the WIT package these bytes encode (printer unverified, tested against wasm-tools component wit)")]
      | .error e => jobj [("text", Json.null), ("note", jstr s!"not a WIT package this decoder reads: {e}")]
    let world := match Silmaril.Wasm.Wit.Tool.projectBytes b with
      | .ok w => jobj [("text", jstr (Wat.print (Silmaril.Wasm.Wit.Tool.worldAst w))),
          ("note", jstr "Silmaril.Wasm.Wit.Project.project: the component's type (its world), as component WAT. Code does not change it (project_stripCode); validity of the result is not proved")]
      | .error e => jobj [("text", Json.null), ("note", jstr s!"not projected: {e}")]
    let summary := jobj [("id", jstr id), ("slug", jstr sl), ("title", jstr title), ("kind", jstr "component"),
      ("source", sourceJson src), ("size", jnat b.size),
      ("imports", jnat imports.length), ("exports", jnat exports.length),
      ("modules", jnat modK), ("components", jnat compK)]
    let validity := match Silmaril.Wasm.Tools.CompValidate.check Silmaril.Wasm.Tools.Features.WFeatures.dflt b with
      | .ok () => jobj [("status", jstr "accepted"), ("note", jstr "Silmaril.Wasm.Tools.CompValidate.check (wasm-tools' default features): a tested transcription of wasmparser's component rules, not proved; only its core-module part is (check_core)")]
      | .error e => jobj [("status", jstr "rejected"), ("note", jstr s!"Silmaril.Wasm.Tools.CompValidate.check (tested transcription, not proved): {e}")]
    let full := jobj [("summary", summary), ("hasBlob", Json.bool true), ("watNote", jstr watNote), ("wit", wit), ("world", world),
      ("validity", validity),
      ("imports", jarr (imports.map fun i => jobj [("name", jstr i.name.name), ("kind", jstr (externDescText i.desc))])),
      ("exports", jarr (exports.map fun e => jobj [("name", jstr e.name.name), ("kind", jstr (sortText e.item.sort)), ("idx", jnat e.item.idx)])),
      ("children", jarr children), ("coreInstances", jarr coreInstJ), ("instances", jarr instJ),
      ("canons", jarr canonJ), ("customs", jarr (customs.map jstr))]
    writeText s!"wasm/c/{sl}.json" full.compress
    modify fun o => { o with components := o.components.push summary }

/-! ## The registry's artifacts -/

structure Artifact where
  name : String := ""
  path : String := ""
  cid : String := ""
  sha256 : String := ""
  layer : String := ""
  deriving Inhabited

def quoted (line : String) : String :=
  match line.splitOn "\"" with
  | _ :: v :: _ => v
  | _ => ""

/-- The Wasm artifacts of `artifacts.toml` (its machine-written layout: one `key = value` line
each, `meta` on one line). -/
def readArtifacts (text : String) : List Artifact := Id.run do
  let mut out : List Artifact := []
  let mut cur : Option Artifact := none
  for line in text.splitOn "\n" do
    if line.startsWith "[[artifact]]" then
      if let some a := cur then out := out ++ [a]
      cur := some default
    else if let some a := cur then
      if line.startsWith "name = " then cur := some { a with name := quoted line }
      else if line.startsWith "paths = " then cur := some { a with path := quoted line }
      else if line.startsWith "cid = " then cur := some { a with cid := quoted line }
      else if line.startsWith "sha256 = " then cur := some { a with sha256 := quoted line }
      else if line.startsWith "meta = " then
        let l := if (line.splitOn "layer = \"component\"").length > 1 then "component"
          else if (line.splitOn "layer = \"module\"").length > 1 then "module" else ""
        cur := some { a with layer := l }
  if let some a := cur then out := out ++ [a]
  return out.filter (·.layer != "")

/-! ## Lean example modules -/

def leanExamples : List (String × String × Module × String) := [
  ("silmaril.wasm.examples.verified.prog", "Examples.Verified.prog (sum, factorial, …)",
    Silmaril.Wasm.Examples.Verified.prog, "Silmaril.Wasm.Examples.Verified.prog"),
  ("silmaril.wasm.examples.rust_door", "Examples.RustInst.door (a compiled Rust door)",
    Silmaril.Wasm.Examples.RustInst.door, "Silmaril.Wasm.Examples.RustInst.door"),
  ("silmaril.wasm.cfg.examples.mod", "Cfg.Examples.mod (br_table dispatcher, special edges)",
    Silmaril.Wasm.Cfg.Examples.mod, "Silmaril.Wasm.Cfg.Examples.mod"),
  ("silmaril.wasm.cfg.examples.effects", "Cfg.Examples.effectsMod (effects inside try_table)",
    Silmaril.Wasm.Cfg.Examples.effectsMod, "Silmaril.Wasm.Cfg.Examples.effectsMod")] ++
  -- the concrete modules of the acceptor interpretation catalog
  Silmaril.Wasi.Accept.Catalog.concreteModules.map fun (id, title, decl, m) =>
    (id, title, m, decl.toString)

/-- SHA-256 of `b`, lower-case hex (`Silmaril.Crypto.SHA256.digest`, compiled). -/
def sha256Hex (b : ByteArray) : String :=
  String.join ((Silmaril.Crypto.SHA256.digest b.data.toList).map fun x =>
    let h := (Nat.toDigits 16 x.toNat)
    String.ofList (if h.length < 2 then '0' :: h else h))

def run (artifactsPath outDir : String) : IO UInt32 := do
  let text ← IO.FS.readFile artifactsPath
  let root := (System.FilePath.mk artifactsPath).parent.bind (·.parent) |>.getD "."
  let arts := readArtifacts text
  -- the Lean example modules, encoded once
  let leans := leanExamples.map fun (id, title, m, decl) =>
    let bytes := match Binaryen.Exe.encodeModule? m with
      | .ok l => some (ByteArray.mk l.toArray) | .error _ => none
    (id, title, m, decl, bytes, bytes.map sha256Hex)
  -- a registered module whose SHA-256 is that of a Lean example's bytes is the same file: it is
  -- published once, as the Lean example (its id and links), with the artifact's CID and path
  let registered (sha : Option String) : Option Artifact :=
    sha.bind fun h => match arts.filter (fun a => a.layer == "module" && a.sha256 == h) with
      | [a] => some a
      | _ => none
  let mergedShas := leans.filterMap fun (_, _, _, _, _, sha) => (registered sha).map (·.sha256)
  let act : M Unit := do
    for a in arts.filter (fun a => !mergedShas.contains a.sha256) do
      let p := root / a.path
      let b ← IO.FS.readBinFile p
      let src : Source := { kind := "artifact", name := a.name, cid := some a.cid,
                            sha256 := some a.sha256, path := some a.path,
                            doc := "a blob registered in silmaril/artifacts.toml" }
      if a.layer == "component" then doComponent a.name a.name src b
      else
        match Binary.Core.Decode.decodeModule b with
        | .ok m => doModule a.name a.name src m (some b)
        | .error e =>
          let summary := jobj [("id", jstr a.name), ("slug", jstr (slug a.name)), ("title", jstr a.name),
            ("kind", jstr "module"), ("source", sourceJson src), ("size", jnat b.size)]
          writeFile s!"wasm/blob/{slug a.name}.wasm" b
          writeText s!"wasm/m/{slug a.name}.json" (jobj [("summary", summary), ("hasBlob", Json.bool true),
            ("unsupported", jstr s!"the module decoder rejected the bytes: {e}")]).compress
          modify fun o => { o with modules := o.modules.push summary }
    for (id, title, m, decl, bytes, sha) in leans do
      let lean := "a Lean value (the proof target is this module AST); the bytes are encoded from it by " ++
        "Silmaril.Wasm.Binaryen.Exe.encodeModule?, which satisfies the specification's binary grammar " ++
        "(encodeModule?_sound: Binary.Core.Encodes bytes m); SHA-256 of exactly these bytes, computed by " ++
        "Silmaril.Crypto.SHA256.digest; "
      let src : Source := match registered sha with
        | some a => { kind := "lean", name := decl, cid := some a.cid, sha256 := sha, path := some a.path,
                      doc := lean ++ s!"registered in silmaril/artifacts.toml as {a.name} ({a.path}), whose " ++
                        "SHA-256 is the same; the CID is that artifact's. A claim about the artifact's bytes " ++
                        "reaches this AST only through a decoding certificate (a value's .is problem)" }
        | none => { kind := "lean", name := decl, sha256 := sha, doc := lean ++ "not registered in artifacts.toml" }
      doModule id title src m bytes
  let ((), out) ← act.run {}
  let index := jobj [("components", jarr out.components.toList), ("modules", jarr out.modules.toList)]
  let files := out.files.push ("wasm/index.json", index.compress.toUTF8)
    |>.push ("wasm/functions.json", (jarr out.functions.toList).compress.toUTF8)
  for (rel, b) in files do
    let p := System.FilePath.mk outDir / rel
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile p b
  IO.println s!"wasm-pages: {out.components.size} components, {out.modules.size} modules, {files.size} files"
  return 0

end WasmPages

def main (args : List String) : IO UInt32 :=
  match args with
  | [a, o] => WasmPages.run a o
  | _ => do IO.eprintln "usage: wasm-pages ARTIFACTS.toml OUTDIR"; return 2
