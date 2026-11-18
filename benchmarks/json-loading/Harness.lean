module

public import Silmaril.Formats.Json.Fast.Elab
public import Silmaril.Formats.JsonWire.Defs
public import Lean.Data.Json.Parser

@[expose] public section
open Silmaril.Formats

inductive Step where
  | key (key : String)
  | index (position : Nat)

def wireMember (key : JsonWire.Units) : JsonWire.Syn JsonWire.Decimal .obj → Option JsonWire.Ast
  | .objNil => none
  | .objCons name value rest => if name == key then some value else wireMember key rest

def wireIndex (position : Nat) : JsonWire.Syn JsonWire.Decimal .arr → Option JsonWire.Ast
  | .nil => none
  | .cons value rest => match position with
    | 0 => some value
    | n + 1 => wireIndex n rest

def wireSelect (source : Option JsonWire.Ast) (path : List Step) : Option Bool := do
  let value ← path.foldlM (fun value step => match step, value with
    | .key name, .map members => wireMember (JsonWire.stringUnits name) members
    | .index position, .list items => wireIndex position items
    | _, _ => none) (← source)
  match value with
  | .scalar (some (.bool result)) => some result
  | _ => none

def fastSelect (indexed : Bool) (source : Except Json.Fast.Error Json.Fast.Value)
    (path : List Step) : Option Bool := do
  let value ← path.foldlM (fun value step => match step with
    | .key name => if indexed then value.member? name else value.memberLinear? name
    | .index position => value.index? position) (← source.toOption)
  value.bool?

def main (args : List String) : IO UInt32 := do
  let [mode, path] := args | throw (IO.userError "expected parser and fixture path")
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let accepted ← IO.mkRef <| match mode with
    | "wire" => (JsonWire.parse? ⟨bytes⟩).isSome
    | "fast" => (Json.Fast.parseBytes bytes).isOk
    | "lean" => ((String.fromUTF8? bytes).map fun text => (Lean.Json.parse text).isOk).getD false
    | _ => false
  let elapsed := (← IO.monoNanosNow) - start
  let accepted ← accepted.get
  IO.println s!"parse_ns={elapsed} accepted={accepted}"
  return if accepted then 0 else 1
