module

public import Silmaril.Formats.Dasl.Encode.Map.Defs
public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Wasm.Wac.Graph.Defs
public import Std.Data.String.ToNat

/-! The `wac/graph/v1` schema serializes the existing function-level WAC `Graph`, not
the WAC text AST or a component-model validator. A package table supplies a `PkgSig`
and a raw component-binary link for each package index. -/

@[expose] public section

namespace Silmaril.Wasm.Wac.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Wasm.Component (ValTy FuncTy Iface)

variable {Binary Name Ref Item Other : Type}

/-- Package row order supplies the numeric package indices used by `Graph.nodes`. -/
structure Composition (Binary : Type) where
  graph : Graph
  packages : List (PkgSig × Binary)

/-- The graph-level resolution predicate, with an explicit package-table range check.
It does not assert that any binary is a component or implements its advertised signature. -/
def Composition.Resolved (value : Composition Binary) : Prop :=
  (∀ inst ∈ value.graph.nodes, inst.pkg < value.packages.length) ∧
    value.graph.WF (fun index => (value.packages[index]?.map Prod.fst).getD default)

abbrev Inline := Tree Empty Empty

def embedInline : Inline → Tree Ref Name := Tree.map Empty.elim Empty.elim

/- No references, including resolved edges, may appear inside graph metadata. -/
def readInline : Tree Ref Name → Option Inline
  | .i64 bits => some (.i64 bits)
  | .bytes bytes => some (.bytes bytes)
  | .string text => some (.string text)
  | .bool value => some (.bool value)
  | .null => some .null
  | .list len values =>
    let items := fun index => readInline (values index)
    if all : ∀ index, (items index).isSome then some (.list len fun index => (items index).get (all index))
    else none
  | .dict keys values =>
    let items := fun key => readInline (values key)
    if all : ∀ key, (items key).isSome then some (.dict keys fun key => (items key).get (all key))
    else none
  | _ => none

/-- Unbounded graph indices use shortest decimal strings, not truncated I64s. -/
def natural : Encode.TotalCodec Nat Inline where
  encode index := .string index.repr
  decode?
    | .string text => do
      let index ← text.toNat?
      if text = index.repr then some index else none
    | _ => none
  recovers index := by simp [Nat.toNat?_repr]

def pairCodec (left : Encode.TotalCodec Item (Tree Ref Name)) (right : Encode.TotalCodec Other (Tree Ref Name)) :
    Encode.TotalCodec (Item × Other) (Tree Ref Name) := (left.prod right).then Encode.pairEntry

def srcWrite : Src → Inline
  | .imp name => Encode.list.encode [.string "import", .string name]
  | .out index name => Encode.list.encode [.string "instance", natural.encode index, .string name]

def srcRead (tree : Inline) : Option Src := do
  match ← Encode.list.decode? tree with
  | [.string "import", .string name] => some (.imp name)
  | [.string "instance", index, .string name] => (natural.decode? index).map (Src.out · name)
  | _ => none

/-- Primitive type spellings of the memory-free ABI (compound types are arrays below). -/
def primitiveWrite : ValTy → String
  | .bool => "bool"
  | .s8 => "s8" | .u8 => "u8" | .s16 => "s16" | .u16 => "u16"
  | .s32 => "s32" | .u32 => "u32" | .s64 => "s64" | .u64 => "u64"
  | .f32 => "f32" | .f64 => "f64" | .char => "char"
  | _ => ""

def primitiveRead : String → Option ValTy
  | "bool" => some .bool
  | "s8" => some .s8 | "u8" => some .u8 | "s16" => some .s16 | "u16" => some .u16
  | "s32" => some .s32 | "u32" => some .u32 | "s64" => some .s64 | "u64" => some .u64
  | "f32" => some .f32 | "f64" => some .f64 | "char" => some .char
  | _ => none

mutual
def typeWrite : ValTy → Inline
  | .record fields => Encode.list.encode (.string "record" :: typesWrite fields)
  | .variant cases => Encode.list.encode (.string "variant" :: casesWrite cases)
  | ty => .string (primitiveWrite ty)
termination_by structural ty => ty

def typesWrite : List ValTy → List Inline
  | [] => []
  | ty :: rest => typeWrite ty :: typesWrite rest
termination_by structural tys => tys

def casesWrite : List (Option ValTy) → List Inline
  | [] => []
  | none :: rest => .null :: casesWrite rest
  | some ty :: rest => typeWrite ty :: casesWrite rest
termination_by structural cases => cases
end

def typeRead : Inline → Option ValTy
  | .string tag => primitiveRead tag
  | .list (_ + 1) values =>
    match values 0 with
    | .string "record" => ((List.ofFn fun index => typeRead (values index.succ)).mapM id).map .record
    | .string "variant" =>
      ((List.ofFn fun index =>
        match values index.succ with
        | .null => some none
        | _ => (typeRead (values index.succ)).map some).mapM id).map .variant
    | _ => none
  | _ => none

def caseRead (tree : Inline) : Option (Option ValTy) :=
  match tree with
  | .null => some none
  | _ => (typeRead tree).map some

def funcTypes (ty : Encode.TotalCodec ValTy Inline) : Encode.TotalCodec FuncTy Inline :=
  (⟨fun value => (value.params, value.results), fun pair => some ⟨pair.1, pair.2⟩, fun _ => rfl⟩ :
    Encode.TotalCodec FuncTy (List ValTy × List ValTy)).then (pairCodec (Encode.listOf ty) (Encode.listOf ty))

def iface (ty : Encode.TotalCodec ValTy Inline) : Encode.TotalCodec Iface Inline :=
  Encode.listOf (pairCodec Encode.text (funcTypes ty))

def arguments (src : Encode.TotalCodec Src Inline) : Encode.TotalCodec (List (String × Src)) Inline :=
  Encode.listOf (pairCodec Encode.text src)

def instances (src : Encode.TotalCodec Src Inline) : Encode.TotalCodec (List Inst) Inline :=
  Encode.listOf ((⟨fun inst => (inst.pkg, inst.args), fun pair => some ⟨pair.1, pair.2⟩, fun _ => rfl⟩ :
    Encode.TotalCodec Inst (Nat × List (String × Src))).then (pairCodec natural (arguments src)))

def graph (ty : Encode.TotalCodec ValTy Inline) (src : Encode.TotalCodec Src Inline) :
    Encode.TotalCodec Graph Inline :=
  (⟨fun value => (value.imports, value.nodes, value.exports),
    fun parts => some ⟨parts.1, parts.2.1, parts.2.2⟩, fun _ => rfl⟩ :
      Encode.TotalCodec Graph (Iface × List Inst × List (String × Src))).then
    (pairCodec (iface ty) (pairCodec (instances src) (arguments src)))

def signature (ty : Encode.TotalCodec ValTy Inline) : Encode.TotalCodec PkgSig Inline :=
  (⟨fun value => (value.imports, value.exports), fun pair => some ⟨pair.1, pair.2⟩, fun _ => rfl⟩ :
    Encode.TotalCodec PkgSig (Iface × Iface)).then (pairCodec (iface ty) (iface ty))

def familyTag : String := "wac/graph/v1"

def envelope : Encode.TotalCodec (Tree Ref Name) (Tree Ref Name) where
  encode body := Encode.pairEntry.encode (.string familyTag, body)
  decode? tree := do
    let (.string label, body) ← Encode.pairEntry.decode? tree | none
    if label = familyTag then some body else none
  recovers _ := rfl

def composition (graph : Encode.TotalCodec Graph (Tree Ref Name))
    (signature : Encode.TotalCodec PkgSig (Tree Ref Name)) (binary : Encode.TotalCodec Binary (Tree Ref Name)) :
    Encode.TotalCodec (Composition Binary) (Tree Ref Name) :=
  ((⟨fun value => (value.graph, value.packages), fun pair => some ⟨pair.1, pair.2⟩, fun _ => rfl⟩ :
    Encode.TotalCodec (Composition Binary) (Graph × List (PkgSig × Binary))).then
      (pairCodec graph (Encode.listOf (pairCodec signature binary)))).then envelope

def rawLink : Encode.TotalCodec Name (Shallow Name) :=
  ⟨fun name => .ref (.blob name), (fun | .ref (.blob name) => some name | _ => none), fun _ => rfl⟩

def rawBlob : Encode.TotalCodec (Name × ByteArray) (Named Name) :=
  ⟨fun binary => .blob binary.1 binary.2, (fun | .blob name bytes => some (name, bytes) | _ => none), fun _ => rfl⟩

def Composition.names (value : Composition (Name × ByteArray)) : Composition Name :=
  ⟨value.graph, value.packages.map fun row => (row.1, row.2.1)⟩

end Silmaril.Wasm.Wac.Dasl
