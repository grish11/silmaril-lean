module

public import Silmaril.Semantics.SQLite.Relational.Executor.Defs
public import Silmaril.Semantics.Relational.UB.QueryDefs

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (QueryRel)
open Silmaril.Relational.UB (ExplicitQuery CatastrophicQuery)

/-- The typed boundary can reject input syntax outside the point-read profile. -/
inductive CheckedRequest (Ref : Type) where
  | invoke (call : Invocation Ref)
  | unsupported (feature : String)

inductive CheckedReply (p : Profile) where
  | statement (result : Result p)
  | unsupported (feature : String)

abbrev CheckedOutcome (p : Profile) := CheckedReply p × Connection p

/-- An admitted invocation or an ordinary rejection sits inside the native
host boundary, which also names a documented undefined C API call. -/
inductive HostRequest (Ref : Type) where
  | checked (request : CheckedRequest Ref)
  | bindFinalized

inductive UBReason where
  | bindFinalized
  deriving DecidableEq, Repr

def invocationEmbedding (Ref : Type) : Invocation Ref ↪ CheckedRequest Ref :=
  ⟨.invoke, @fun _ _ h => CheckedRequest.invoke.inj h⟩

def checkedEmbedding (Ref : Type) : CheckedRequest Ref ↪ HostRequest Ref :=
  ⟨.checked, @fun _ _ h => HostRequest.checked.inj h⟩

variable {p : Profile}

def CheckedOutcome.ofStatement (out : Outcome p) : CheckedOutcome p :=
  (.statement out.1, out.2)

/-- Scope rejection has its own result and leaves the connection intact. -/
def CheckedRequest.denote (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)) :
    QueryRel (Connection p) (CheckedRequest p.Ref) (CheckedOutcome p)
  | db, .invoke call => sem.observe CheckedOutcome.ofStatement db call
  | db, .unsupported feature => fun out => (.unsupported feature, db) = out

def Executor.check (exec : Executor p) (db : Connection p) :
    CheckedRequest p.Ref → CheckedOutcome p
  | .invoke call => CheckedOutcome.ofStatement (exec.execute db call)
  | .unsupported feature => (.unsupported feature, db)

noncomputable def HostRequest.explicit
    (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)) :
    ExplicitQuery (Connection p) (HostRequest p.Ref) (CheckedOutcome p) UBReason :=
  (ExplicitQuery.ofQueryRel (CheckedRequest.denote sem)).extendUB
    (checkedEmbedding p.Ref) .bindFinalized

noncomputable def HostRequest.catastrophic
    (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)) :
    CatastrophicQuery (Connection p) (HostRequest p.Ref) (CheckedOutcome p) :=
  (CatastrophicQuery.ofQueryRel (CheckedRequest.denote sem)).extendUB
    (checkedEmbedding p.Ref)

end Silmaril.SQLite.Relational
