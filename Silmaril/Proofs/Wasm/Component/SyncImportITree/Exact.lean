module

public import Silmaril.Wasm.Component.SyncImportITree.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
import Silmaril.Wasm.Abstract.BodyTrace.Pending.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Game.Termination.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.SyncImportITree

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Elgot
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Abstract.BodyTrace
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {c : SimpleI} {o : GrowOracle} {r : Ready c} {q : Question (exportIface c)}
  {f : r.inst.F.Op} {x : Cursor}

private theorem cut_unique {left right : Cut r.inst f}
    (hl : ReachesCut o r.inst f x left) (hr : ReachesCut o r.inst f x right) : left = right := by
  cases left with
  | request e p =>
    cases right with
    | request e' p' =>
      have hm : Sum.inl (.ask e) = (Sum.inl (.ask e') : Move r.inst.E r.inst.F) :=
        ScalarInstance.Trans.player_unique hl hr trivial
      have he : e = e' := by simpa using hm
      subst e'
      have hs : ScalarInstance.HState.waiting f p.1 p.2 e = .waiting f p'.1 p'.2 e :=
        ScalarInstance.Trans.functional hl hr
      obtain ⟨hs, ht⟩ : p.1 = p'.1 ∧ p.2 = p'.2 := by simpa using hs
      exact congrArg (Cut.request e) (Prod.ext hs ht)
    | reply a s =>
      have hm : Sum.inl (.ask e) = (Sum.inr (.ans f a) : Move r.inst.E r.inst.F) :=
        ScalarInstance.Trans.player_unique hl hr trivial
      cases hm
  | reply a s =>
    cases right with
    | request e p =>
      have hm : Sum.inr (.ans f a) = (Sum.inl (.ask e) : Move r.inst.E r.inst.F) :=
        ScalarInstance.Trans.player_unique hl hr trivial
      cases hm
    | reply a' s' =>
      have hm : Sum.inr (.ans f a) = (Sum.inr (.ans f a') : Move r.inst.E r.inst.F) :=
        ScalarInstance.Trans.player_unique hl hr trivial
      have ha : a = a' := by simpa using hm
      subst a'
      have hs : ScalarInstance.HState.idle (I := r.inst) s = .idle s' :=
        ScalarInstance.Trans.functional hl hr
      exact congrArg (Cut.reply a) (ScalarInstance.HState.idle.inj hs)

private theorem cut_not_silent {cut : Cut r.inst f}
    (h : ReachesCut o r.inst f x cut) : ¬ Silent o x := by
  cases cut with
  | request e p =>
    unfold ReachesCut at h
    cases h with
    | ucall run callout _ => exact reach_normal_not_infinite run (calloutAt_no_internal callout)
  | reply a s =>
    unfold ReachesCut at h
    cases h with
    | oret run result _ => exact reach_normal_not_infinite run (resultAt_no_internal result)

theorem head_eq_iff {front : Front c q} (available : front ≠ .unavailable) :
    head o r q f x = front ↔ ReachesFront o r q f x front := by
  classical
  by_cases hc : ∃ cut, ReachesCut o r.inst f x cut
  · rw [head, dite_eq_left hc]
    exact ⟨fun h => .inl ⟨_, hc.choose_spec, h⟩, fun h => by
      rcases h with ⟨cut, reached, eq⟩ | ⟨quiet, _⟩
      · rwa [cut_unique hc.choose_spec reached]
      · exact False.elim (cut_not_silent hc.choose_spec quiet)⟩
  · rw [head, dite_eq_right hc]
    unfold ReachesFront
    rw [or_iff_right (fun ⟨cut, reached, _⟩ => hc ⟨cut, reached⟩)]
    by_cases hs : Silent o x
    · simp only [hs, ite_true, true_and]
      exact eq_comm
    · simp [hs, Ne.symm available]

private noncomputable def render (o : GrowOracle) (r : Ready c) (q : Question (exportIface c))
    (f : r.inst.F.Op) (x : Cursor) : Front c q →
      ITree.Tree (Silmaril.Wasm.Abstract.Body.SigEv (signature c.imports)) (BodyResult q)
  | .request m k => ITree.vis (R := m.Answer) ⟨m, rfl⟩ fun a => tree o r q f (k a)
  | .reply a s => ITree.ret (.ok (⟨.reply a⟩, ⟨s⟩))
  | .quiet => ITree.diverge
  | .unavailable => ITree.ret (.ok (⟨.noOutcome⟩, ⟨x.1⟩))

private theorem tree_at (front : Front c q) (h : head o r q f x = front) :
    tree o r q f x = render o r q f x front := by
  conv => lhs; unfold tree; rw [ITree.iterate_fixpoint (unfoldStep o r q f)]
  cases front with
  | request m k =>
    simp only [unfoldStep, h, render, tree]
    refine (ITree.vis_bind _ _ _).trans ?_
    congr 1
    funext a
    simp
  | reply | unavailable => simp [unfoldStep, h, render]; rfl
  | quiet => simp [unfoldStep, h, render]

theorem tree_request {m : Question c.imports} {k : m.Answer → Cursor}
    (h : ReachesFront o r q f x (.request m k)) :
    tree o r q f x = ITree.vis (R := m.Answer) ⟨m, rfl⟩ (fun a => tree o r q f (k a)) :=
  tree_at _ ((head_eq_iff (by simp)).mpr h)

theorem tree_reply {a : q.Answer} {s} (h : ReachesFront o r q f x (.reply a s)) :
    tree o r q f x = ITree.ret (.ok (⟨.reply a⟩, ⟨s⟩)) :=
  tree_at _ ((head_eq_iff (by simp)).mpr h)

theorem tree_quiet (h : Silent o x) : tree o r q f x = ITree.diverge :=
  tree_at _ ((head_eq_iff (by simp)).mpr (.inr ⟨h, rfl⟩))

variable {cs : List (Call (signature c.imports))} {obs : Observation q}

private theorem sees_request {m : Question c.imports}
    {k : m.Answer → ITree.Tree (Silmaril.Wasm.Abstract.Body.SigEv (signature c.imports)) (BodyResult q)}
    (h : Sees (ITree.vis (R := m.Answer) ⟨m, rfl⟩ k) cs obs) :
    (cs = [] ∧ obs = .pending m) ∨
      ∃ a tail, cs = ⟨m, a⟩ :: tail ∧ Sees (k a) tail obs := by
  cases obs with
  | pending n =>
    rcases Pend.vis_cases h with ⟨hcs, rfl⟩ | ⟨a, tail, rfl, hp⟩
    · exact .inl ⟨hcs, rfl⟩
    · exact .inr ⟨a, tail, rfl, hp⟩
  | reply a s =>
    obtain ⟨n, tail, rfl, hp⟩ := path_vis_inv h
    exact .inr ⟨n, tail, rfl, hp⟩
  | quiet =>
    obtain ⟨n, tail, rfl, hp⟩ := path_vis_inv h
    exact .inr ⟨n, tail, rfl, hp⟩

private theorem sees_ret {out : BodyResult q} (h : Sees (ITree.ret out) cs obs) :
    ∃ a s, cs = [] ∧ obs = .reply a s ∧ out = .ok (⟨.reply a⟩, ⟨s⟩) := by
  cases obs with
  | reply a s =>
    obtain ⟨hs, hr⟩ := path_ret_iff.mp h
    exact ⟨a, s, hs, rfl, PathEnd.val.inj hr.symm⟩
  | pending m =>
    change Pend (ITree.ret out) cs m at h
    cases h with
    | here eq => exact False.elim (ITree.ret_ne_vis _ _ _ eq)
    | vis eq _ => exact False.elim (ITree.ret_ne_vis _ _ _ eq)
  | quiet =>
    obtain ⟨_, hr⟩ := path_ret_iff.mp h
    cases hr

private theorem sees_diverge (h : Sees ITree.diverge cs obs) : cs = [] ∧ obs = .quiet := by
  cases obs with
  | reply a s =>
    change Path ITree.diverge cs (.val (Except.ok (⟨Completion.reply a⟩, ⟨s⟩) : BodyResult q)) at h
    cases h with
    | ret eq => exact False.elim (ITree.ret_ne_diverge _ eq.symm)
    | vis eq _ => exact False.elim (ITree.vis_ne_diverge _ _ eq.symm)
  | pending m =>
    change Pend ITree.diverge cs m at h
    cases h with
    | here eq => exact False.elim (ITree.vis_ne_diverge _ _ eq.symm)
    | vis eq _ => exact False.elim (ITree.vis_ne_diverge _ _ eq.symm)
  | quiet =>
    change Path ITree.diverge cs .div at h
    cases h with
    | div _ => exact ⟨rfl, rfl⟩
    | vis eq _ => exact False.elim (ITree.vis_ne_diverge _ _ eq.symm)

private theorem observes_of_sees (h : Sees (tree o r q f x) cs obs) :
    Observes o r q f x cs obs := by
  induction cs generalizing x with
  | nil =>
    cases hfront : head o r q f x with
    | request m k =>
      rw [tree_at _ hfront, render] at h
      rcases sees_request h with ⟨_, rfl⟩ | ⟨_, _, eq, _⟩
      · exact .pending ((head_eq_iff (by simp)).mp hfront)
      · cases eq
    | reply a s =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨a', s', _, rfl, eq⟩ := sees_ret h
      cases eq
      exact .reply ((head_eq_iff (by simp)).mp hfront)
    | quiet =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨_, rfl⟩ := sees_diverge h
      rcases (head_eq_iff (by simp)).mp hfront with ⟨cut, _, eq⟩ | ⟨hs, _⟩
      · cases cut <;> simp only [cutFront] at eq
        · split at eq
          · split at eq <;> cases eq
          · cases eq
        · cases eq
      · exact .quiet hs
    | unavailable =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨_, _, _, _, eq⟩ := sees_ret h
      cases eq
  | cons call tail ih =>
    cases hfront : head o r q f x with
    | request m k =>
      rw [tree_at _ hfront, render] at h
      rcases sees_request h with ⟨eq, _⟩ | ⟨a, rest, eq, hn⟩
      · cases eq
      · cases eq
        exact .answer a ((head_eq_iff (by simp)).mp hfront) (ih hn)
    | reply a s =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨_, _, eq, _, _⟩ := sees_ret h
      cases eq
    | quiet =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨eq, _⟩ := sees_diverge h
      cases eq
    | unavailable =>
      rw [tree_at _ hfront, render] at h
      obtain ⟨_, _, eq, _, _⟩ := sees_ret h
      cases eq

theorem sees_iff : Sees (tree o r q f x) cs obs ↔ Observes o r q f x cs obs := by
  refine ⟨observes_of_sees, fun h => ?_⟩
  induction h with
  | reply h => exact .ret (tree_reply h)
  | pending h => exact .here (tree_request h)
  | quiet h => exact .div (tree_quiet h)
  | @answer _ _ _ _ obs a h _ ih =>
    cases obs with
    | reply => exact Path.vis (n := a) (tree_request h) ih
    | pending => exact Pend.vis (n := a) (tree_request h) ih
    | quiet => exact Path.vis (n := a) (tree_request h) ih

theorem productive_iff {calls : Stream' (Call (signature c.imports))} :
    InfPath (tree o r q f x) calls ↔
      ∀ n, ∃ m, Observes o r q f x (Stream'.take n calls) (.pending m) := by
  rw [infPath_iff_pend]
  exact forall_congr' fun n => exists_congr fun m =>
    sees_iff (o := o) (r := r) (q := q) (f := f) (x := x) (cs := Stream'.take n calls)
      (obs := .pending m)

end Silmaril.Proofs.Wasm.Component.SyncImportITree
