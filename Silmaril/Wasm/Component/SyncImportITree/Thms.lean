module

public import Silmaril.Wasm.Component.SyncImportITree.Defs
public import Mathlib.Data.Stream.Init
import Silmaril.Proofs.Wasm.Component.SyncImportITree.Exact
import Silmaril.Proofs.Wasm.Component.SyncImportITree.ABI

public section

namespace Silmaril.Wasm.Component.SyncImportITree

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Elgot
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Step Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Abstract.BodyTrace

variable {c : SimpleI} {o : GrowOracle} {r : Ready c} {q : Question (exportIface c)}
  {f : r.inst.F.Op} {x : Cursor}

/-- Every typed export question of a ready component has a Core entry. -/
theorem entry_exists (r : Ready c) (q : Question (exportIface c)) :
    ∃ f, entry r q = some f :=
  Silmaril.Proofs.Wasm.Component.SyncImportITree.entry_exists r q

/-- At an import cut, the tree exposes the typed request. The answer selects
a residual tree at the corresponding resumed Core cursor. -/
theorem tree_request {m : Question c.imports} {k : m.Answer → Cursor}
    (h : ReachesFront o r q f x (.request m k)) :
    tree o r q f x = ITree.vis (R := m.Answer) ⟨m, rfl⟩ (fun a => tree o r q f (k a)) :=
  Silmaril.Proofs.Wasm.Component.SyncImportITree.tree_request h

/-- Each legal reply takes the existing game resume transition. Its component
and Core values satisfy the existing canonical-import relation, and the
transition resumes the actual Core callout in one Core reduction. -/
theorem request_resumes {m : Question c.imports} {k : m.Answer → Cursor}
    (reached : ReachesFront o r q f x (.request m k)) (a : m.Answer) :
    ∃ (e : r.inst.E.Op) (p : Cursor) (b : r.inst.E.Ar e),
      ReachesCut o r.inst f x (.request e p) ∧
      r.inst.Trans (profile o) (.waiting f p.1 p.2 e) (.inl (.ans e b))
        (.running f (k a).1 (k a).2) ∧
      b.toResult = (match a with
        | none => .trap
        | some vs => .values ((lowerArgs c.imports[m.index].2.results vs.val).map
            Silmaril.Wasm.SingleThreaded.ofFlat)) ∧
      ImpRel c r.inst ⟨e, b⟩ [⟨(m.index, .vals m.args.val), a.map (fun vs => .vals (Subtype.val vs))⟩] ∧
      ∃ h args, CalloutAt p.1 p.2 h args ∧
        Step (profile o) (answerHost h args b.toResult) (p.2.config p.1) ((k a).2.config (k a).1) :=
  Silmaril.Proofs.Wasm.Component.SyncImportITree.request_resumes reached a

/-- Exact finite observation at a running or resumed cursor. The result
includes pending requests, replies with their stores, and witnessed silent
divergence after any finite sequence of legal exchanges. -/
theorem sees_iff {cs : List (Call (signature c.imports))} {obs : Observation q} :
    Sees (tree o r q f x) cs obs ↔ Observes o r q f x cs obs :=
  Silmaril.Proofs.Wasm.Component.SyncImportITree.sees_iff

/-- An infinite sequence of answered imports is a tree path exactly when
each finite prefix reaches a further request in the Core/ABI model. -/
theorem productive_iff {calls : Stream' (Call (signature c.imports))} :
    InfPath (tree o r q f x) calls ↔
      ∀ n, ∃ m, Observes o r q f x (Stream'.take n calls) (.pending m) :=
  Silmaril.Proofs.Wasm.Component.SyncImportITree.productive_iff

/-- Exact finite observation from the supplied ready store at export entry. -/
theorem body_sees_iff {s : Store Nat} {cs : List (Call (signature c.imports))}
    {obs : Observation q} (h : entry r q = some f) :
    Sees ((body o r q).run ⟨s⟩).run cs obs ↔
      Observes o r q f (s, r.inst.initThread f) cs obs := by
  simpa only [body, StateT.run, ExceptT.run, ExceptT.mk, h] using
    (sees_iff (o := o) (x := (s, r.inst.initThread f)) (cs := cs) (obs := obs))

end Silmaril.Wasm.Component.SyncImportITree
