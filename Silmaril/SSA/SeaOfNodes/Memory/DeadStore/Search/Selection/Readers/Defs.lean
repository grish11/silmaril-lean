module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Defs

/-! # Infer the reader certificate for one checked dead Store -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers

open RVSDG (Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- Infer the address obligations from the nominated Store up to its first
same-wire overwrite. The result still requires the existing rewrite checks. -/
def discover (graph : Graph args) (removeVersion : Nat) : Option (Certificate args) :=
  atVersion graph
where
  beforeOverwrite (observed : Port args .address) :
      {past : List (List ValueSort)} → {version : Nat} →
      Body args past version → Option (List (Port args .address))
    | _, _, .ret _ _ => none
    | _, _, .load _ (.arg reader) rest => (beforeOverwrite observed rest).map (reader :: ·)
    | _, _, .load _ (.output _ _) _ => none
    | _, _, .store _ address _ rest =>
      if (Certificate.mk observed []).matches address then some [] else beforeOverwrite observed rest

  atVersion : {past : List (List ValueSort)} → {version : Nat} →
      Body args past version → Option (Certificate args)
    | _, _, .ret _ _ => none
    | _, _, .load _ _ rest => atVersion rest
    | _, version, .store _ address _ rest =>
      if version + 1 = removeVersion then
        match address with
        | .arg observed => (beforeOverwrite observed rest).map (Certificate.mk observed)
        | .output _ _ => none
      else atVersion rest

/-- Try original Store versions oldest first, using their inferred reader
ports. The existing checker decides concrete cell inequalities at this input. -/
def rewrite (graph : Graph args) (input : Tuple (Val cells) args) : Option (Selection.Result args) :=
  (Selection.storeVersions graph).findSome? fun version => do
    let facts ← discover graph version
    Selection.tryStore graph input version facts

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers
