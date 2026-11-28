module

public import Silmaril.Semantics.Page.Defs
public import Silmaril.Semantics.ReadWrite.Defs

/-! Numbered-page stores and programs as clients of the shared read/write trace API. -/

@[expose] public section
namespace Silmaril.Semantics.Page

universe u v w a
variable {Id : Type u} {Content : Type v} {Memory : Type w}

def Store.access (store : Store Id Content Memory) : ReadWrite.Access Id Content Memory where
  read memory page := (store.lookup memory page).value
  write memory page value :=
    match store.lookup memory page with
    | .absent => none
    | _ => some (store.set memory page (.defined value))

/-- The successful writes in the page program's edit vocabulary. -/
def writeEdits (writes : ReadWrite.WriteTrace Id Content) : List (Edit Id Content) :=
  writes.map fun (page, value) => .write page value

/-- A normally returning path through a page program, with actual read replies
recorded and store validation supplied separately by trace replay.
The path uses reads and writes on a fixed domain. -/
inductive Program.Records {α : Type a} : Program Id Content α → ReadWrite.Trace Id Content → α → Prop
  | pure {value} : Records (.pure value) [] value
  | left {l r trace result} : Records l trace result → Records (.choose l r) trace result
  | right {l r trace result} : Records r trace result → Records (.choose l r) trace result
  | read {page value next trace result} : Records (next (.value value)) trace result →
      Records (.call (.read page) next) (.read page value :: trace) result
  | write {page value next trace result} : Records (next .written) trace result →
      Records (.call (.write page value) next) (.write page value :: trace) result

end Silmaril.Semantics.Page
