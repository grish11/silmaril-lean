module

public import Silmaril.Formats.SExp.Proper
public import Silmaril.Formats.Dasl.Encode.Defs
public import Lean.Data.Json
public import Std.Data.String.ToInt
public import Std.Data.String.ToNat
public import Silmaril.Courses.Cambridge.L1.Syntax

/-! Shared structural presentation for Cambridge AST codecs. Proper S-expressions
give ordered constructor trees. The JSON presentation uses arrays for lists and
strings for atoms. In particular, integers have exact decimal string payloads. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.AstCodec

open Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)

abbrev Tree := SExp String
abbrev Codec (α : Type) := TotalCodec α Tree

variable {α β : Type}

def node (tag : String) (fields : List Tree) : Tree := SExp.ofList (.atom tag :: fields)

def fold (atom : String → α) (list : List α → α) : Tree → α
  | .atom value => atom value
  | .list _ children => list (List.ofFn fun i => fold atom list (children i))

theorem fold_ofList (atom : String → α) (list : List α → α) (children : List Tree) :
    fold atom list (SExp.ofList children) = list (children.map (fold atom list)) := by
  change list (List.ofFn (fun i => fold atom list children[i])) = _
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The bottom-up result identifies the syntactic category of every child. -/
inductive Datum (Ty Term : Type) where
  | atom (value : String)
  | type (value : Ty)
  | term (value : Term)
  | typeField (name : String) (value : Ty)
  | termField (name : String) (value : Term)

def taggedReader {Ty Term : Type}
    (readFields : String → List (Datum Ty Term) → Option (Datum Ty Term)) :
    List (Datum Ty Term) → Option (Datum Ty Term)
  | .atom tag :: fields => readFields tag fields
  | _ => none

def readTree {Ty Term : Type} (readNode : List (Datum Ty Term) → Option (Datum Ty Term)) :
    Tree → Option (Datum Ty Term) :=
  fold (fun value => some (.atom value))
    (fun children => children.mapM id >>= readNode)

@[simp] theorem readTree_atom {Ty Term : Type}
    (readNode : List (Datum Ty Term) → Option (Datum Ty Term)) (value : String) :
    readTree readNode (.atom value) = some (.atom value) := rfl

@[simp] theorem readTree_node {Ty Term : Type}
    (readNode : List (Datum Ty Term) → Option (Datum Ty Term))
    (tag : String) (fields : List Tree) :
    readTree readNode (node tag fields) =
      (do let children ← fields.mapM (readTree readNode)
          readNode (.atom tag :: children)) := by
  unfold node readTree
  rw [fold_ofList]
  simp [fold, List.mapM_map, Function.comp_def, Option.bind_assoc]

def Datum.getTerm {Ty Term : Type} : Datum Ty Term → Option Term
  | .term value => some value
  | _ => none

def Datum.getType {Ty Term : Type} : Datum Ty Term → Option Ty
  | .type value => some value
  | _ => none

def readInt (text : String) : Option Int := do
  let value ← text.toInt?
  if value.repr = text then some value else none

def readNat (text : String) : Option Nat := do
  let value ← text.toNat?
  if value.repr = text then some value else none

@[simp] theorem readInt_repr (n : Int) : readInt n.repr = some n := by simp [readInt]
@[simp] theorem readNat_repr (n : Nat) : readNat n.repr = some n := by simp [readNat]

def opName : L1.Op → String
  | .add => "add"
  | .ge => "ge"

def readOp : String → Option L1.Op
  | "add" => some .add
  | "ge" => some .ge
  | _ => none

@[simp] theorem readOp_opName (op : L1.Op) : readOp (opName op) = some op := by
  cases op <;> rfl

def boolName (b : Bool) : String := if b then "true" else "false"

def readBool : String → Option Bool
  | "true" => some true
  | "false" => some false
  | _ => none

@[simp] theorem readBool_boolName (b : Bool) : readBool (boolName b) = some b := by
  cases b <;> rfl

def envelope (language sort : String) (tree : Tree) : Tree :=
  node "cambridge-ast-v1" [.atom language, .atom sort, tree]

def readEnvelope (language sort : String) (tree : Tree) : Option Tree :=
  match tree.children? with
  | some [.atom "cambridge-ast-v1", .atom lang, .atom kind, payload] =>
    if lang = language ∧ kind = sort then some payload else none
  | _ => none

def versioned (language sort : String) (codec : Codec α) : Codec α where
  encode value := envelope language sort (codec.encode value)
  decode? tree := readEnvelope language sort tree >>= codec.decode?
  recovers value := by simp [envelope, node, readEnvelope, codec.recovers]

/-- Map lists to arrays and scalar string atoms to JSON strings. -/
def toJson : Tree → Lean.Json :=
  fold Lean.Json.str (fun children => .arr children.toArray)

def ofJson : Lean.Json → Option Tree
  | .str value => some (.atom value)
  | .arr children => (children.toList.mapM ofJson).map SExp.ofList
  | _ => none
termination_by tree => sizeOf tree
decreasing_by
  have hs := Array.sizeOf_lt_of_mem (show _ ∈ children from by simpa using ‹_ ∈ children.toList›)
  simp_wf
  omega

theorem mapM_ofFn_some {n : Nat} (f : Fin n → α) (g : α → Option β)
    (values : Fin n → β) (h : ∀ i, g (f i) = some (values i)) :
    (List.ofFn f).mapM g = some (List.ofFn values) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, List.mapM_cons, h]
    rw [ih (fun i => f i.succ) (fun i => values i.succ) (fun i => h i.succ)]
    rfl

theorem ofJson_toJson (tree : Tree) : ofJson (toJson tree) = some tree := by
  induction tree with
  | atom value => simp [toJson, fold, ofJson]
  | list n children ih =>
    change ofJson (.arr (List.ofFn (fun i => toJson (children i))).toArray) = _
    rw [ofJson]
    rw [mapM_ofFn_some _ _ _ ih]
    simp only [Option.map_some, Option.some.injEq]
    change SExp.list (List.ofFn children).length (fun i => (List.ofFn children)[i]) = _
    have h : (List.ofFn children).length = n := List.length_ofFn
    have hf : (fun i : Fin (List.ofFn children).length => (List.ofFn children)[i]) ≍ children :=
      (Fin.heq_fun_iff h).mpr (by intro i; simp)
    let left : Σ k, Fin k → Tree := ⟨_, fun i => (List.ofFn children)[i]⟩
    let right : Σ k, Fin k → Tree := ⟨n, children⟩
    exact congrArg (fun value : Σ k, Fin k → Tree => SExp.list value.1 value.2)
      (show left = right from Sigma.ext h hf)

def jsonPresentation : TotalCodec Tree Lean.Json := ⟨toJson, ofJson, ofJson_toJson⟩

def asJson (codec : Codec α) : TotalCodec α Lean.Json := codec.then jsonPresentation

theorem encode_injective (codec : TotalCodec α β) : Function.Injective codec.encode := by
  intro left right h
  have hd := congrArg codec.decode? h
  rw [codec.recovers, codec.recovers] at hd
  exact Option.some.inj hd

end Silmaril.Courses.Cambridge.AstCodec
