module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs

/-! # Executable histories of the selected finite request tree -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Assignment)

deriving instance DecidableEq for Event

/-- A finite ordered word and the two observable fields of the typed return. -/
structure History where
  events : List Event
  exit : Bool
  payload : Bool
deriving DecidableEq

def History.observation (h : History) : Observation :=
  (.ok (terminal h.exit h.payload), FreeMonoid.ofList h.events)

def replies : List Reply :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- Enumerate every admitted tag and payload, updating the selected child's
environment with the payload from that same recorded event. -/
def Tree.histories : {n : Nat} → Tree n → Assignment n → List History
  | _, .ret right i, env => [⟨[], right, env i⟩]
  | _, .ask label query l r, env => replies.flatMap fun reply =>
    (if reply.1 then r.histories (env.push reply.2) else l.histories (env.push reply.2)).map fun h =>
      { h with events := event label (query.eval env) reply :: h.events }

/-- A history witnessed by one of the two actual packed programs. -/
structure Difference where
  guard : Bool
  fromRight : Bool
  history : History
deriving DecidableEq

def Difference.source (w : Difference) (p q : Tree 1) : Tree 1 :=
  if w.fromRight then q else p

def Difference.target (w : Difference) (p q : Tree 1) : Tree 1 :=
  if w.fromRight then p else q

def Tree.candidates (p q : Tree 1) : List Difference :=
  [false, true].flatMap fun g =>
    (p.histories (fun _ => g)).map (fun h => ⟨g, false, h⟩) ++
    (q.histories (fun _ => g)).map (fun h => ⟨g, true, h⟩)

/-- Search the reachable histories at both caller guards, in both directions. -/
def Tree.separate? (p q : Tree 1) : Option Difference :=
  (p.candidates q).find? fun w =>
    decide (w.history ∉ (w.target p q).histories (fun _ => w.guard))

namespace Example

/-- Both programs share their first request and left continuation. Their
right continuations disagree on whether to stop or make another request. -/
def shorter : Tree 1 :=
  .ask false (.read 0) (.ret false 0) (.ret true 0)

def deeper : Tree 1 :=
  .ask false (.read 0) (.ret false 0) (.ask true (.read 0) (.ret false 1) (.ret true 1))

end Example
end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
