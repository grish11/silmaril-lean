module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.IR
public import Silmaril.Proofs.Wasm.Component.InstSem.WiredExport
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ComposeX

/-!
# The IR's export phase (`Task.exportIR`)

* **The reading's layout** (`refRead_layout`): after the inline core instances of the definitions
  before the first core instantiation, the reading's core instances are the nodes', each at its
  base in the environment (after the imports and the exports of the nodes before it);
* **the IR's export call** (`InstSem.denI_ex_node`): the first export, the option-less lift of
  environment function `e`, makes one call of `e`; the call is answered by the node owning `e`,
  after its instantiation, without calls below;
* **the node's run** (`InstSem.engineI_ex_inv`): the node's engine instance runs its start
  function, then the export from the store it leaves; the export's run makes no import call
  (`exportRun_nil`: an import call of a typed run has one `i32` argument, so the wiring `lowF`
  calls `f`, a call below);
* **`exportIR`**: `Task.exportIR`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Proofs.Wasm.Component.DecoderBridge (RDef)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.SingleThreaded (Internal status neverFail profile)

/-! ## The reading's layout -/

/-- The number of function exports `coreIface` reads off a module (`0` outside the fragment). -/
def ifaceWidth (m : Silmaril.Wasm.Module) : Nat :=
  match coreIface m with
  | .ok (_, _, e) => e.length
  | .error _ => 0

/-- **The nodes' core instances in the environment**: from `e₀`, each node's instance is at the
base its predecessors leave, with the exports `coreIface` reads off its module. -/
inductive Layout : Nat → List RCI → List (Silmaril.Wasm.Module × List Impl) → Nat → Prop
  | nil (e : Nat) : Layout e [] [] e
  | snoc {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
      {m : Silmaril.Wasm.Module} {w : List Impl} {nm : List (String × String)} {im exps : CoreIface} :
      Layout e₀ cis ns e → coreIface m = .ok (nm, im, exps) →
      Layout e₀ (cis ++ [.node e exps]) (ns ++ [(m, w)]) (e + exps.length)

theorem Layout.len {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
    (h : Layout e₀ cis ns e) :
    cis.length = ns.length ∧ e = e₀ + (ns.map fun q => ifaceWidth q.1).sum := by
  induction h with
  | nil => exact ⟨rfl, by simp⟩
  | snoc _ hc ih =>
    refine ⟨by simp [ih.1], ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, ifaceWidth, hc, ih.2]
    omega

theorem Layout.get {e₀ e : Nat} {cis : List RCI} {ns : List (Silmaril.Wasm.Module × List Impl)}
    (h : Layout e₀ cis ns e) {k base : Nat} {exps : CoreIface}
    (hk : cis[k]? = some (.node base exps)) :
    ∃ m w nm im, ns[k]? = some (m, w) ∧ coreIface m = .ok (nm, im, exps) ∧
      base = e₀ + ((ns.take k).map fun q => ifaceWidth q.1).sum := by
  induction h with
  | nil => cases hk
  | @snoc e cis ns m w nm im exps' hL hc ih =>
    have hl := hL.len
    by_cases hlt : k < cis.length
    · rw [List.getElem?_append_left hlt] at hk
      obtain ⟨m', w', nm', im', h1, h2, h3⟩ := ih hk
      refine ⟨m', w', nm', im', ?_, h2, ?_⟩
      · rw [List.getElem?_append_left (by omega), h1]
      · rw [List.take_append_of_le_length (by omega), h3]
    · rw [List.getElem?_append_right (by omega)] at hk
      have hk' : k = cis.length := by
        rcases Nat.lt_or_ge k (cis.length + 1) with h' | h'
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
      subst hk'
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, RCI.node.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      refine ⟨m, w, nm, im, ?_, hc, ?_⟩
      · rw [List.getElem?_append_right (by omega), hl.1]; simp
      · rw [hl.1, List.take_left' rfl, hl.2]

/-- The invariant of the reading after the first core instantiation: the core instances are the
first `A` followed by the nodes', laid out from `e₀`. -/
def LayInv (e₀ : Nat) (A : List RCI) (R : RSt) : Prop :=
  ∃ cis, R.coreInsts = A ++ cis ∧ Layout e₀ cis R.nodes R.env

theorem refStep_layInv {e₀ : Nat} {A : List RCI} {R R' : RSt} {d : RDef}
    (hd : ∀ its, d ≠ .coreInstance (.exports its)) (h : refStep R d = some R')
    (hI : LayInv e₀ A R) : LayInv e₀ A R' := by
  obtain ⟨cis, hc, hl⟩ := hI
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; exact ⟨cis, hc, hl⟩)
    | exact absurd rfl (hd _)
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  case h_4 =>
    obtain ⟨m, -, ⟨names, im, exps⟩, hci, w, -, h⟩ := h
    cases h
    have hci' : coreIface m = .ok (names, im, exps) := by
      cases hc' : coreIface m with
      | error e => rw [hc'] at hci; cases hci
      | ok v => rw [hc'] at hci; cases hci; rfl
    exact ⟨cis ++ [.node R.env exps], by simp [hc], .snoc hl hci'⟩
  all_goals (unfold LayInv; aesop)

theorem foldlM_layInv {e₀ : Nat} {A : List RCI} :
    ∀ {ds : List RDef} {R R' : RSt}, (∀ d ∈ ds, ∀ its, d ≠ .coreInstance (.exports its)) →
      ds.foldlM refStep R = some R' → LayInv e₀ A R → LayInv e₀ A R'
  | [], R, R', _, h, hI => by simp at h; subst h; exact hI
  | d :: ds, R, R', hd, h, hI => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      exact foldlM_layInv (fun d' h' => hd d' (.tail _ h')) h
        (refStep_layInv (hd d (.head _)) hR hI)

theorem refStep_pre {R R' : RSt} {d : RDef} (hd : ¬ IsInst d) (h : refStep R d = some R') :
    R'.nodes = R.nodes ∧ R'.env = R.env ∧
      ∃ L : List RCI, R'.coreInsts = R.coreInsts ++ L ∧ L.length = (preInsts [d]).length ∧
        ∀ ci ∈ L, ∃ es, ci = .inline es := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl, [], by simp, by simp [preInsts], by simp⟩)
    | exact absurd trivial hd
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  case h_5 =>
    obtain ⟨es, -, h⟩ := h
    cases h
    exact ⟨rfl, rfl, [.inline es], rfl, by simp [preInsts], by simp⟩
  all_goals aesop (add norm preInsts)

theorem foldlM_pre :
    ∀ {ds : List RDef} {R R' : RSt}, (∀ d ∈ ds, ¬ IsInst d) → ds.foldlM refStep R = some R' →
      R'.nodes = R.nodes ∧ R'.env = R.env ∧
        ∃ L : List RCI, R'.coreInsts = R.coreInsts ++ L ∧ L.length = (preInsts ds).length ∧
          ∀ ci ∈ L, ∃ es, ci = .inline es
  | [], R, R', _, h => by simp at h; subst h; exact ⟨rfl, rfl, [], by simp, by simp [preInsts], by simp⟩
  | d :: ds, R, R', hd, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      obtain ⟨h1, h2, L₁, hL₁, hl₁, hi₁⟩ := refStep_pre (hd d (.head _)) hR
      obtain ⟨h1', h2', L₂, hL₂, hl₂, hi₂⟩ := foldlM_pre (fun d' h' => hd d' (.tail _ h')) h
      have hp : (preInsts (d :: ds)).length = (preInsts [d]).length + (preInsts ds).length := by
        cases d with
        | coreInstance ci => cases ci <;> simp [preInsts, Nat.add_comm]
        | _ => simp [preInsts]
      refine ⟨h1'.trans h1, h2'.trans h2, L₁ ++ L₂, by rw [hL₂, hL₁, List.append_assoc], ?_, ?_⟩
      · rw [List.length_append, hl₁, hl₂, hp]
      · intro ci hci
        rcases List.mem_append.1 hci with h | h
        · exact hi₁ ci h
        · exact hi₂ ci h

theorem refStep_imports_len {R R' : RSt} {d : RDef} (h : refStep R d = some R') :
    R'.imports.length = R.imports.length + (if isFuncImport d then 1 else 0) := by
  unfold refStep at h
  split at h
  all_goals first
    | (cases h; simp [isFuncImport])
    | cases h
    | (simp only [bind, Option.bind_eq_some_iff] at h)
  all_goals aesop (add norm isFuncImport)

theorem foldlM_imports_len :
    ∀ {ds : List RDef} {R R' : RSt}, ds.foldlM refStep R = some R' →
      R'.imports.length = R.imports.length + (ds.filter isFuncImport).length
  | [], R, R', h => by simp at h; subst h; simp
  | d :: ds, R, R', h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hR : refStep R d with
    | none => simp [hR] at h
    | some R1 =>
      simp only [hR] at h
      rw [foldlM_imports_len h, refStep_imports_len hR, List.filter_cons]
      split
      · simp; omega
      · simp

/-- **The reading's layout**: the reading's imports are the component's function imports; its core
instances are the inline instances of the definitions before the first core instantiation,
followed by the nodes', laid out from the imports. -/
theorem refRead_layout {r : RefComponent} {R : RSt} {pre : List RDef} {mi : Nat}
    {cargs : List (String × Nat)} {post : List RDef} (hR : refRead r = some R)
    (hfc : firstCore? r = some (pre, mi, cargs, post))
    (hpost : ∀ d ∈ post, ∀ its, d ≠ .coreInstance (.exports its)) :
    R.imports.length = (r.filter isFuncImport).length ∧
      ∃ A : List RCI, A.length = (preInsts pre).length ∧ (∀ ci ∈ A, ∃ es, ci = .inline es) ∧
        LayInv R.imports.length A R := by
  have hi := foldlM_imports_len hR
  simp only at hi
  refine ⟨by simpa using hi, ?_⟩
  have hnoI := firstCore?_noInst r hfc
  have hs := firstCore?_eq r hfc
  subst hs
  unfold refRead at hR
  rw [List.foldlM_append] at hR
  simp only [bind, Option.bind_eq_some_iff, List.foldlM_cons] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  obtain ⟨hn₁, he₁, L, hL, hc₁, hin⟩ := foldlM_pre hnoI h₁
  simp only [refStep, bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨m, -, ⟨names, im, exps⟩, hci, w, -, h₂⟩ := h₂
  injection h₂ with h₂
  have hci' : coreIface m = .ok (names, im, exps) := by
    cases hc' : coreIface m with
    | error e => rw [hc'] at hci; cases hci
    | ok v => rw [hc'] at hci; cases hci; rfl
  refine ⟨R₁.coreInsts, by simpa [hL] using hc₁, by simpa [hL] using hin, ?_⟩
  have hI : LayInv R₁.env R₁.coreInsts R₂ := by
    subst h₂
    refine ⟨[.node R₁.env exps], rfl, ?_⟩
    simp only [hn₁]
    exact .snoc (cis := []) (ns := []) (.nil _) hci'
  have := foldlM_layInv hpost hR hI
  rw [he₁] at this
  simpa [hi] using this

theorem forall₂_get_left {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ {j : Nat} {b : β}, l₂[j]? = some b →
      ∃ a, l₁[j]? = some a ∧ P a b
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .cons hp _, 0, _, h => by cases h; exact ⟨_, rfl, hp⟩
  | _ :: _, _ :: _, .cons _ hr, j + 1, _, h => forall₂_get_left hr h

theorem nodeW_width {p : Binary.CoreMod × List Impl} {q : Silmaril.Wasm.Module × List Impl}
    (h : NodeW (.core p.1 p.2) q) : ifaceWidth q.1 = (CoreModule.exports p.1).length := by
  obtain ⟨cm, he, -, hci⟩ := h
  injection he with he₁ he₂
  subst he₁
  simp [ifaceWidth, hci]

/-- The reading's nodes, taken `j` at a time, have the IR nodes' widths. -/
theorem width_take :
    ∀ {ps : List (Binary.CoreMod × List Impl)} {ns : List (Silmaril.Wasm.Module × List Impl)},
      List.Forall₂ NodeW (coreNodes ps) ns → ∀ j,
        ((ns.take j).map fun q => ifaceWidth q.1).sum = coreWidth (ps.take j)
  | [], [], .nil, j => by simp [coreWidth]
  | p :: ps, q :: ns, .cons h hs, 0 => by simp [coreWidth]
  | p :: ps, q :: ns, .cons h hs, j + 1 => by
    have ih := width_take hs j
    simp only [coreWidth] at ih
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, coreWidth, ih,
      nodeW_width (p := p) h]

/-- **A node core instance of the reading is an IR node's**: the `j`-th after the inline instances,
with the IR node's exports, at its base in the IR's environment. -/
theorem node_of_layout {n : Nat} {A : List RCI} {R : RSt} {ps : List (Binary.CoreMod × List Impl)}
    (hA : ∀ ci ∈ A, ∃ es, ci = .inline es) (hI : LayInv n A R)
    (hN : List.Forall₂ NodeW (coreNodes ps) R.nodes) {k base : Nat} {exps : CoreIface}
    (hk : R.coreInsts[k]? = some (.node base exps)) :
    ∃ j p, k = A.length + j ∧ ps[j]? = some p ∧ CoreModule.exports p.1 = exps ∧
      base = n + coreWidth (ps.take j) := by
  obtain ⟨cis, hc, hL⟩ := hI
  rw [hc] at hk
  by_cases hlt : k < A.length
  · rw [List.getElem?_append_left hlt] at hk
    obtain ⟨es, he⟩ := hA _ (List.mem_of_getElem? hk)
    cases he
  · rw [List.getElem?_append_right (by omega)] at hk
    obtain ⟨m, w, nm, im, hm, hci, hb⟩ := hL.get hk
    obtain ⟨x, hx, hW⟩ := forall₂_get_left hN hm
    simp only [coreNodes, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨cm, he, -, hci'⟩ := hW
    injection he with he₁ he₂
    subst he₁
    rw [hci] at hci'
    injection hci' with hci'
    simp only [Prod.mk.injEq] at hci'
    refine ⟨k - A.length, p, by omega, hp, hci'.2.2.symm, ?_⟩
    rw [hb, width_take hN]

/-! ## Typed runs of an export -/

section Typed

open Silmaril.Wasm.Execution.Core (Store StoreOk ConfigOk)
open Silmaril.Wasm.SingleThreaded (ThreadOk)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-- An IR configuration typed at the result types `ts`, with host functions of core type
`fFlat`. -/
structure RTNt (S : Store Nat) (t : STh) (ts : List Silmaril.Wasm.Validation.CValType) : Prop where
  store : StoreOk S
  thread : ThreadOk S t ts
  hosts : HostTy S

theorem rtNt_run {ts : List Silmaril.Wasm.Validation.CValType} {x y : Store Nat × STh}
    (h : Relation.ReflTransGen (Internal neverFail) x y) (hR : RTNt x.1 x.2 ts) :
    RTNt y.1 y.2 ts := by
  obtain ⟨hs, ht⟩ := Silmaril.Wasm.SingleThreaded.reachable_typed h hR.store hR.thread
  have hf := funcs_steps h
  exact ⟨hs, ht, fun fi hfi => hR.hosts fi (by rw [← hf]; exact hfi)⟩

theorem args_of_calloutNt {ts : List Silmaril.Wasm.Validation.CValType} {S : Store Nat} {t : STh}
    (hR : RTNt S t ts) {h : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hst : status neverFail S t = .callout h args) :
    ∃ b : BitVec 32, args = [.num ⟨.int .i32, b⟩] := by
  obtain ⟨fi, hfi, hcode, ps, rs, hexp, hargs⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.callout_args_typed hR.store hR.thread hst
  have hty := hR.hosts fi hfi h hcode
  rw [hty] at hexp
  have he := Silmaril.Wasm.Execution.Core.Expand.func_eq hexp
    (Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat))
  injection he with he₁ he₂
  rw [he₁] at hargs
  simp only [Param.v1Type, fFlat, List.map_cons, List.map_nil,
    Silmaril.Wasm.Validation.Ty.toList_ofList] at hargs
  rcases hargs with _ | ⟨hv, hrest⟩
  cases hrest
  obtain ⟨b, rfl⟩ := Silmaril.Wasm.Execution.Core.ValOk.int_inv hv
  exact ⟨b, rfl⟩

/-- The invocation of a function without arguments is not a callout, when host functions take
one argument. -/
theorem invoke_not_callout {S : Store Nat} (hT : HostTy S) {a : Nat} {h : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} :
    status neverFail S (Silmaril.Wasm.SingleThreaded.Thread.invoke a []) ≠ .callout h args := by
  intro hst
  obtain ⟨E, a', hd⟩ := Silmaril.Wasm.SingleThreaded.status_callout_inv hst
  let ty : Silmaril.Wasm.Validation.DefType := (S.funcs[a]?.map Silmaril.Wasm.Execution.Core.FuncInst.type).getD default
  have hcode : ((Silmaril.Wasm.SingleThreaded.Thread.invoke a []).config S).code =
      Silmaril.Wasm.Execution.Core.vals [.ref (.func a)] ++ .callRefType ty :: [] := by
    simp [Silmaril.Wasm.SingleThreaded.Thread.config, Silmaril.Wasm.SingleThreaded.Thread.invoke,
      Silmaril.Wasm.Execution.Core.invoke,
      Silmaril.Wasm.Execution.Core.vals, Silmaril.Wasm.Execution.Core.Val.toAdmin, ty]
  rw [hcode, Silmaril.Wasm.SingleThreaded.decompose?_of_split
    (Silmaril.Wasm.SingleThreaded.splitVals_vals_cons rfl [])] at hd
  simp only [Silmaril.Wasm.SingleThreaded.decompHead, Silmaril.Wasm.Execution.Core.Admin.isCallRef,
    ite_true, Silmaril.Wasm.SingleThreaded.topRedex, List.getLast?_singleton] at hd
  split at hd
  · rename_i h' n hh
    obtain ⟨fi, ps, rs, hfi, hc, hexp, rfl⟩ := Silmaril.Wasm.SingleThreaded.hostArity?_eq_some hh
    have hty := hT fi (List.mem_of_getElem? hfi) h' hc
    rw [hty] at hexp
    have he := Silmaril.Wasm.Execution.Core.Expand.func_eq hexp
      (Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat))
    injection he with he₁ he₂
    rw [he₁] at hd
    simp [Param.v1Type, fFlat, Silmaril.Wasm.Validation.Ty.length] at hd
  · cases hd

/-- **The export's run makes no import call**: from a typed store whose host functions have core
type `fFlat`, an import call of the run of an export invoked without arguments has one `i32`
argument, which the wiring `lowF` makes a call of `f`, a call below. -/
theorem exportRun_nil {imps : CoreIface} {w : List Impl} (hw : ∀ im ∈ w, im = lowF)
    (hwl : imps.length ≤ w.length) {S : Store Nat} (hs : StoreOk S) (hT : HostTy S) {a : Nat}
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)} {c'' : irEng.Config Nat}
    (hrun : Param.StartRunI irEng imps (S, irEng.invoke a []) cs c'')
    {ys : List (Round sigU (sigN imps.length))} (hys : cs = ys.map Round.call)
    (hr : ∀ y ∈ ys, Prog.Runs (implsN 1 w imps.length y.q) y.cs y.a)
    (hnil : ∀ y ∈ ys, y.cs = []) : cs = [] := by
  cases hrun with
  | nil run => rfl
  | @call _ s₁ _ t₁ h args _ _ run callout hh r rest =>
    exfalso
    cases ys with
    | nil => cases hys
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hys
      obtain ⟨hy, -⟩ := hys
      unfold Engine.CoreEngine.Steps at run
      rw [internalP_eqN] at run
      have run' : Relation.ReflTransGen (Internal neverFail)
          (S, Silmaril.Wasm.SingleThreaded.Thread.invoke a []) (s₁, t₁) := run
      obtain ⟨args', hst', hfl⟩ :=
        Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' callout
      have hs₁ : status neverFail s₁ t₁ = .callout h args' :=
        (statusP_profile s₁ t₁).symm.trans hst'
      rcases Relation.ReflTransGen.cases_head run' with he | ⟨y₁, hy₁, -⟩
      · cases he
        exact invoke_not_callout hT hs₁
      · obtain ⟨s₂, t₂⟩ := y₁
        obtain ⟨f₂, code₂, -, hstep⟩ := hy₁
        obtain ⟨pre, args₀, fi, ps, rs, code, hv, hfi, hexp, hn, -, -⟩ :=
          Silmaril.Proofs.Wasm.Game.invoke_step_shape hstep
        have ha₀ : args₀ = [] := (List.append_eq_nil_iff.mp hv.symm).2
        subst ha₀
        have hps : ps.toList = [] := List.eq_nil_of_length_eq_zero hn.symm
        obtain ⟨-, ps', rs', -, -, hok⟩ := Silmaril.Wasm.Execution.Core.invoke_ok hs
          ⟨fi, ps, rs, hfi, hexp, by rw [hps]; exact .nil⟩
        have hR : RTNt S (Silmaril.Wasm.SingleThreaded.Thread.invoke a []) rs'.toList :=
          ⟨hs, hok, hT⟩
        have hR₁ := rtNt_run run' hR
        obtain ⟨b, rfl⟩ := args_of_calloutNt hR₁ hs₁
        simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
        cases hfl
        obtain ⟨yq, ycs, ya⟩ := y
        simp only [Round.call, Sigma.mk.injEq] at hy
        obtain ⟨rfl, -⟩ := hy
        obtain ⟨k, hk, -⟩ := implsN_lowF hw (n := imps.length) (h := ⟨h, hh⟩) (by simp; omega) b
        have hy₀ := hr _ (.head _)
        rw [hnil _ (.head _)] at hy₀
        simp only at hy₀
        rw [hk] at hy₀
        cases hy₀

/-- **A typed start run with lowered imports, each call answered `()`, ends typed.** -/
theorem startRun_rtn {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true)
    {w : List Impl} (hw : ∀ im ∈ w, im = lowF) (hwl : imps.length ≤ w.length) :
    ∀ {c c' : irEng.Config Nat} {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)},
      Param.StartRunI irEng imps c cs c' → RTN c.1 c.2 →
      ∀ {ys : List (Round sigU (sigN imps.length))}, cs = ys.map Round.call →
      (∀ y ∈ ys, Prog.Runs (implsN 1 w imps.length y.q) y.cs y.a) →
      (∀ x ∈ allCalls ys, x.2 = InstTests.unitV) → RTN c'.1 c'.2 := by
  intro c c' cs hrun
  induction hrun with
  | nil run =>
    intro hR _ _ _ _
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    exact rtN_run run hR
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest ih =>
    intro hR ys hys hruns hu
    cases ys with
    | nil => cases hys
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hys
      obtain ⟨hy, hys⟩ := hys
      unfold Engine.CoreEngine.Steps at run
      rw [internalP_eqN] at run
      have hR₁ : RTN s₁ t₁ := rtN_run run hR
      obtain ⟨args', hst', hfl⟩ :=
        Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' callout
      have hs₁ : status neverFail s₁ t₁ = .callout h args' :=
        (statusP_profile s₁ t₁).symm.trans hst'
      obtain ⟨b, rfl⟩ := args_of_calloutN hR₁ hs₁
      simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
      cases hfl
      obtain ⟨yq, ycs, ya⟩ := y
      simp only [Round.call, Sigma.mk.injEq] at hy
      obtain ⟨rfl, hya⟩ := hy
      have hya' : r = ya := eq_of_heq hya
      subst hya'
      obtain ⟨k, hk, hk'⟩ := implsN_lowF hw (n := imps.length) (h := ⟨h, hh⟩) (by simp; omega) b
      have hrun₀ := hruns _ List.mem_cons_self
      simp only at hrun₀
      rw [hk] at hrun₀
      cases hrun₀ with
      | @call _ _ n' cs'' _ hrk =>
        have hn' : n' = InstTests.unitV := hu ⟨(0, .vals [.u32 b]), n'⟩ (by simp [allCalls])
        subst hn'
        simp only [InstTests.unitV] at hrk
        rw [hk'] at hrk
        cases hrk
        have himp : imps[h].2 = fFlat := by
          have := List.all_eq_true.mp himps _ (List.getElem_mem hh)
          simpa using this
        have eres : (core3P (profile neverFail)).resume s₁ t₁
            (Param.resultOf imps[h].2.results (some (.flat []))) =
            Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := by
          rw [himp, resultOf_fFlat]
          rfl
        have hR₂ : RTN s₁ ((core3P (profile neverFail)).resume s₁ t₁
            (Param.resultOf imps[h].2.results (some (.flat [])))) := by
          rw [eres]
          exact rtN_resume hR₁ hs₁
        exact ih hR₂ hys (fun y hy => hruns y (List.mem_cons_of_mem _ hy))
          (fun x hx => hu x (by simp only [allCalls, List.cons_append, List.nil_append]; exact
            List.mem_cons_of_mem _ hx))

end Typed

/-! ## A node's export call -/

/-- The engine instance of a module of the fragment, with its module instance and export
addresses. -/
theorem instOfI_mi {m : Silmaril.Wasm.Module} {imps exps : CoreIface}
    (himps : imps.all (·.2 == fFlat) = true) {J : Param.IInstance irEng}
    (hJ : Param.instOfI irEng m imps exps = some J) :
    ∃ mi, Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
        some (J.store, mi, J.start) ∧ Param.exportAddrs irEng mi exps = some J.addrs := by
  have hA := allocHosts_ir (profile neverFail) imps 0 himps
  rw [irStore_zero, Nat.zero_add, range'_zero] at hA
  have hprep : (core3P (profile neverFail)).prepare?
      (irStore imps.length) m ((List.range imps.length).map
        (core3P (profile neverFail)).ofFunc) =
      Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) := rfl
  have e : Param.allocHosts (core3P (profile neverFail))
      ((core3P (profile neverFail)).empty Nat) 0 imps =
      (irStore imps.length, List.range imps.length) := hA
  unfold Param.instOfI at hJ
  rw [e] at hJ
  dsimp only at hJ
  rw [hprep] at hJ
  cases hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
      ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) with
  | none => rw [hp] at hJ; cases hJ
  | some p =>
    obtain ⟨s', mi, st⟩ := p
    rw [hp] at hJ
    dsimp only at hJ
    obtain ⟨addrs, ha, rfl⟩ := Option.map_eq_some_iff.mp hJ
    exact ⟨mi, rfl, ha⟩

/-- An export address is the function the module instance exports under the export's name. -/
theorem lookup_of_exportAddrs {mi : irEng.Inst} {exps : CoreIface}
    {addrs : List irEng.FuncAddr} (h : Param.exportAddrs irEng mi exps = some addrs) {k : Nat}
    (hk : k < exps.length) {a : Nat} (ha : addrs[k]? = some a) :
    (irEng.exports mi).lookup exps[k].1 = some (.func a) := by
  have hF := List.mapM_eq_some_iff_forall₂.mp h
  obtain ⟨b, hb, hx⟩ := forall₂_get hF (List.getElem?_eq_getElem hk)
  rw [ha] at hb
  cases hb
  change ((irEng.exports mi).lookup exps[k].1).bind irEng.asFunc? = some a at hx
  revert hx
  cases (irEng.exports mi).lookup exps[k].1 with
  | none => intro hx; cases hx
  | some ext =>
    intro hx
    change Silmaril.Wasm.Component.Engine.Core3.asFunc? ext = some a at hx
    cases ext <;> first | (cases hx; rfl) | cases hx

/-- The store of a module of the fragment after preparation is typed, its host functions of core
type `fFlat`. -/
theorem prepared_typed {m : Silmaril.Wasm.Module} {n : Nat}
    {s' : Silmaril.Wasm.Execution.Core.Store Nat} {mi : Silmaril.Wasm.Execution.Core.ModuleInst}
    {st : Option Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore n) m
      ((List.range n).map Silmaril.Wasm.Execution.Core.ExternAddr.func) = some (s', mi, st)) :
    Silmaril.Wasm.Execution.Core.StoreOk s' ∧ HostTy s' ∧
      ∀ f, st = some f → RTN s' (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
  obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed (storeOk_irStore n) hp
  have hT : HostTy s' := by
    intro fi hfi h hcode
    rw [hnew] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · simp only [irStore, List.mem_map, List.mem_range] at hfi
      obtain ⟨i, -, rfl⟩ := hfi
      rfl
    · obtain ⟨c, hc⟩ := hwasm fi hfi
      rw [hc] at hcode
      cases hcode
  exact ⟨hs', hT, fun f hf => ⟨hs', hcfg f hf, hT⟩⟩

/-- **A node's instantiation and export call, without calls below**: the node's engine instance
ends its start function at a node end `x` with the instantiation's calls; the export `k`, named
as the module exports it, runs host-free from the store the start function left to the values
answered. -/
theorem node_export {p : Binary.CoreMod × List Impl} (hno : NodeOk p)
    {tj : List (Call sigU)} (hu : ∀ x ∈ tj, x.2 = InstTests.unitV) {k : Nat} {y : Payload}
    (h : roundsMoves [instRound (F := sigU) tj .ready, exRound (R := Unit)
      (⟨(k, .flat []), [], some y⟩ : Round sigU sigU)] ∈
      coreNodeI (Binary.coreModSemI (profile neverFail)) hostI.length p.1 p.2) :
    ∃ (x : NodeRun) (hk : k < (CoreModule.exports p.1).length) (a : Nat) (c' : irEng.Config Nat)
      (ys : List Flat), x.calls = tj ∧ NodeEnd hostI.length p.1 p.2 x ∧
      (irEng.exports x.minst).lookup ((CoreModule.exports p.1)[k]).1 = some (.func a) ∧
      Engine.CoreEngine.Steps irEng (x.store, irEng.invoke a []) c' ∧
      irEng.status c'.1 c'.2 = .returned (.values ys) ∧ y = .flat ys := by
  obtain ⟨xs₁, xs₂, hruns, htj, hcs, hcase⟩ := coreNodeI_ex_inv h
  rcases hcase with ⟨hn, -⟩ | ⟨hk, hE⟩
  · cases hn
  change _ ∈ Param.engineStrategyI irEng (Param.instOfI irEng (Binary.coreModule p.1)
    (CoreModule.imports p.1) (CoreModule.exports p.1)) (CoreModule.imports p.1)
    (CoreModule.exports p.1) at hE
  obtain ⟨J, hJ, s', hst, a, xs, c'', ys, hcal, hrun, hstat, rfl⟩ := engineI_ex_inv hE
  -- the callee
  simp only [Param.callee?] at hcal
  split at hcal
  · rename_i hft
    obtain ⟨a', ha', he⟩ := Option.map_eq_some_iff.mp hcal
    cases he
    obtain ⟨mi, hprep, haddrs⟩ := instOfI_mi hno.imps hJ
    have hlk := lookup_of_exportAddrs haddrs hk ha'
    have hruns₁ : ∀ y ∈ xs₁, Prog.Runs (implsN hostI.length p.2 _ y.q) y.cs y.a :=
      fun y hy => hruns y (List.mem_append_left _ hy)
    have hruns₂ : ∀ y ∈ xs₂, Prog.Runs (implsN hostI.length p.2 _ y.q) y.cs y.a :=
      fun y hy => hruns y (List.mem_append_right _ hy)
    obtain ⟨hsJ, hTJ, hRJ⟩ := prepared_typed hprep
    -- the start function and the store it leaves
    obtain ⟨hs's, hT', hNE⟩ : Silmaril.Wasm.Execution.Core.StoreOk s' ∧ HostTy s' ∧
        ∃ ys' : List (Σ _ : (sigN (CoreModule.imports p.1).length).Op, Option Payload),
          List.Forall₂ (fun y z => ∃ k, implsN hostI.length p.2 (CoreModule.imports p.1).length y.1 =
            .call z.1 k ∧ k z.2 = .pure y.2) ys' tj ∧
          ((J.start = none ∧ ys' = [] ∧ s' = J.store) ∨
            ∃ f c' vs, J.start = some f ∧
              Param.StartRunI irEng (CoreModule.imports p.1) (J.store, irEng.invoke f []) ys' c' ∧
              irEng.status c'.1 c'.2 = .returned (.values vs) ∧ s' = c'.1) := by
      rcases hst with ⟨hf, hnil, rfl⟩ | ⟨f, c', vs, hf, hrun₀, hst₀, rfl⟩
      · have hx₁ : xs₁ = [] := by
          cases xs₁ with
          | nil => rfl
          | cons _ _ => cases hnil
        subst hx₁
        subst htj
        exact ⟨hsJ, hTJ, [], .nil, .inl ⟨hf, rfl, rfl⟩⟩
      · have hR := hRJ f hf
        have hu' : ∀ x ∈ allCalls xs₁, x.2 = InstTests.unitV := htj ▸ hu
        have hF := startRun_calls hno.imps hno.wires hno.wl hrun₀ hR rfl hruns₁ hu'
        have hR' := startRun_rtn hno.imps hno.wires hno.wl hrun₀ hR rfl hruns₁ hu'
        refine ⟨hR'.store, hR'.hosts, xs₁.map Round.call, htj ▸ hF, .inr ⟨f, c', vs, hf, hrun₀,
          hst₀, rfl⟩⟩
    -- the export's run makes no call
    have hnil₂ : ∀ y ∈ xs₂, y.cs = [] := allCalls_eq_nil hcs.symm
    have h₀ := exportRun_nil hno.wires hno.wl hs's hT' hrun rfl hruns₂ hnil₂
    rw [h₀] at hrun
    obtain ⟨ys', hF, hst'⟩ := hNE
    refine ⟨⟨tj, J, mi, s'⟩, hk, a, c'', ys, rfl, ⟨hJ, hprep, ys', hF, hst'⟩, hlk, ?_, hstat, rfl⟩
    cases hrun with
    | nil run => exact run
  · cases hcal

/-! ## The export on top -/

/-- `liftArgs` at `u32`. -/
theorem liftArgs_u32 {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h : liftArgs [.u32] ys = some ws) : ∃ v : BitVec 32, ys = [⟨.int .i32, v⟩] ∧ ws = [.u32 v] := by
  unfold liftArgs at h
  split at h
  · rename_i vs hl
    cases h
    match ys, hl with
    | ⟨.int .i32, v⟩ :: r, hl =>
      simp only [ValTy.liftList, ValTy.lift, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨v, rfl, rfl⟩
    | [], hl => simp [ValTy.liftList, ValTy.lift] at hl
    | ⟨.int .i64, _⟩ :: _, hl => simp [ValTy.liftList, ValTy.lift] at hl
    | ⟨.float _, _⟩ :: _, hl => simp [ValTy.liftList, ValTy.lift] at hl
  · cases h

/-- **The option-less lift of `func() -> u32` of a call of `e`, called without arguments**: one
call of `e` without arguments (in range), its answer lifted. -/
theorem runs_liftGet {env e : Nat} {cs : List (Call sigU)} {a : Option Payload}
    (h : Prog.Runs (Impl.prog env ⟨[.lift getTy], .call e⟩ (.vals [])) cs a) :
    (∃ r : Option Payload, e < env ∧ cs = [⟨(e, .flat []), r⟩] ∧
      a = r.bind (Adapter.lift getTy).up) ∨ a = none := by
  simp only [Impl.prog, runChain, Adapter.down, getTy, checkLower, ValTy.checkList, ↓reduceIte,
    lowerArgs, ValTy.lowerList, Option.map_some, Target.prog] at h
  by_cases he : e < env
  · simp only [he, ↓reduceIte, Prog.bind] at h
    cases h with
    | call h =>
      cases h
      exact .inl ⟨_, he, rfl, rfl⟩
  · simp only [he, ↓reduceIte, Prog.bind] at h
    cases h
    exact .inr rfl

theorem coreWidth_take_succ {M : Type} [CoreModule M] {ps : List (M × List Impl)} {j : Nat}
    {p : M × List Impl} (hp : ps[j]? = some p) :
    coreWidth (ps.take (j + 1)) = coreWidth (ps.take j) + (CoreModule.exports p.1).length := by
  rw [List.take_add_one, hp, coreWidth_append]
  simp [coreWidth]

theorem coreWidth_take_mono {M : Type} [CoreModule M] (ps : List (M × List Impl)) {a b : Nat}
    (h : a ≤ b) : coreWidth (ps.take a) ≤ coreWidth (ps.take b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, coreWidth_append]
  omega

/-- **Each environment function is exported by at most one node.** -/
theorem node_unique {M : Type} [CoreModule M] {ps : List (M × List Impl)} {o j j' : Nat}
    {p p' : M × List Impl} (hp : ps[j]? = some p) (hp' : ps[j']? = some p') {e : Nat}
    (h₁ : o + coreWidth (ps.take j) ≤ e)
    (h₂ : e < o + coreWidth (ps.take j) + (CoreModule.exports p.1).length)
    (h₁' : o + coreWidth (ps.take j') ≤ e)
    (h₂' : e < o + coreWidth (ps.take j') + (CoreModule.exports p'.1).length) : j = j' := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · have := coreWidth_take_mono ps (show j + 1 ≤ j' by omega)
    rw [coreWidth_take_succ hp] at this
    omega
  · exact h
  · have := coreWidth_take_mono ps (show j' + 1 ≤ j by omega)
    rw [coreWidth_take_succ hp'] at this
    omega

/-! ## `Task.exportIR` -/

theorem forall₂_set {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ {j : Nat} {a : α} {b : β},
      l₁[j]? = some a → P a b → List.Forall₂ P l₁ (l₂.set j b)
  | _, _, .nil, _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, .cons _ hr, 0, _, _, h, hab => by cases h; exact .cons hab hr
  | _ :: _, _ :: _, .cons hp hr, j + 1, _, _, h, hab => .cons hp (forall₂_set hr h hab)

/-- The nodes' instantiation plays, as node ends with their calls. -/
theorem ends_of_plays :
    ∀ {ps : List (Binary.CoreMod × List Impl)} {ts : List (List (Call sigU))},
      List.Forall₂ (fun p tj => instPlay (F := sigU) tj .ready ∈
        coreNodeI (Binary.coreModSemI (profile neverFail)) hostI.length p.1 p.2) ps ts →
      (∀ p ∈ ps, NodeOk p) → (∀ x ∈ ts.flatten, x.2 = InstTests.unitV) →
      ∃ xs : List NodeRun, xs.map NodeRun.calls = ts ∧
        List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs
  | [], [], .nil, _, _ => ⟨[], rfl, .nil⟩
  | p :: ps, t :: ts, .cons h hs, hok, hu => by
    have hp := hok p List.mem_cons_self
    have hc := nodeCalls_of_play hp.imps hp.wl hp.wires hp.names
      (fun x hx => hu x (by simp only [List.flatten_cons]; exact List.mem_append_left _ hx)) h
    obtain ⟨x, rfl, hx⟩ := nodeEnd_of_calls hp hc
    obtain ⟨xs, rfl, hxs⟩ := ends_of_plays hs (fun q hq => hok q (List.mem_cons_of_mem _ hq))
      (fun x' hx' => hu x' (by simp only [List.flatten_cons]; exact List.mem_append_right _ hx'))
    exact ⟨x :: xs, rfl, .cons hx hxs⟩

theorem isGetTy_eq {ft : FuncTy} (h : isGetTy ft = true) : ft = getTy := by
  unfold isGetTy at h
  split at h
  · rfl
  · cases h

theorem liftsCall_eq {im : Impl} (h : liftsCall im = true) :
    ∃ e, im = ⟨[.lift getTy], .call e⟩ := by
  unfold liftsCall at h
  split at h
  · next ft e => exact ⟨e, by rw [isGetTy_eq h]⟩
  · cases h

/-- A definition after the first core instantiation is not an inline core instance. -/
theorem postDefOk_not_inline {n : Nat} {insts : List (List (String × Nat))}
    {mods : List Silmaril.Wasm.Module} {d : RDef} (h : postDefOk n insts mods d = true) :
    ∀ its, d ≠ .coreInstance (.exports its) := by
  rintro its rfl
  simp [postDefOk] at h

/-- **`Task.exportIR`.** -/
theorem exportIR : Task.exportIR := by
  intro b c r ps t n ws hpc hr _ hf himp hnodes hex hu hp
  have hok := nodeOk_frag hpc hr hf hnodes
  obtain ⟨-, hw, ⟨R, hR, -, hget⟩, pre, mi, cargs, post, hfc, -, hpostOk⟩ := multiImpFrag_inv hf
  obtain ⟨R₁, hR₁, hlift⟩ := multiImpFrag_lifts hf
  rw [hR] at hR₁
  cases hR₁
  obtain ⟨R₁, hR₁, hIm, hEx, hN⟩ := relW_of_decode hpc hr (inFrag_of_hostWired hw)
  rw [hR] at hR₁
  cases hR₁
  -- the first export
  obtain ⟨x₀, xr, hx⟩ : ∃ x₀ xr, R.exports = x₀ :: xr := by
    cases h : R.exports with
    | nil => rw [hEx, h] at hex; cases hex
    | cons x₀ xr => exact ⟨x₀, xr, rfl⟩
  rw [hx] at hget hlift
  rw [hEx, hx] at hex
  simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hex
  simp only [List.head?_cons, Option.map_some, Option.getD_some] at hget hlift
  obtain ⟨xn, xty, ⟨xch, xtg⟩⟩ := x₀
  simp only at hex hget hlift
  subst hex
  have hty := isGetTy_eq hget
  subst hty
  obtain ⟨e, he⟩ := liftsCall_eq hlift
  injection he with he₁ he₂
  subst he₁ he₂
  -- the IR's play
  obtain ⟨I, ns, xs'⟩ := c
  have hEx' : xs' = R.exports := hEx
  have hIm' : I = R.imports := hIm
  have hN' : List.Forall₂ NodeW ns R.nodes := hN
  subst himp hnodes
  have hiw : ImportWired hostI.length ps := by
    intro p hp im him
    rw [(hok p hp).wires im him]
    show (0 : Nat) < 1
    omega
  have hone : ∀ cs, Prog.Runs (exportsH (envAfter hostI.length (coreNodes ps)) xs'
      (0, .vals [])) cs (some (.vals ws)) → ∃ y, cs = [⟨(e, .flat []), some y⟩] := by
    intro cs hcs
    simp only [exportsH, implsH, hEx', hx, List.map_cons, List.getElem?_cons_zero] at hcs
    rcases runs_liftGet hcs with ⟨r', -, rfl, hr'⟩ | hnone
    · cases r' with
      | none => cases hr'
      | some y => exact ⟨y, rfl⟩
    · cases hnone
  obtain ⟨y, hrunP, ts, rfl, hF, j, p, tj, hpj, htj, hle, hlt, hnode⟩ := denI_ex_node hiw hone hp
  -- the answer
  obtain ⟨v, rfl, rfl⟩ : ∃ v : BitVec 32, y = .flat [⟨.int .i32, v⟩] ∧ ws = [.u32 v] := by
    simp only [exportsH, implsH, hEx', hx, List.map_cons, List.getElem?_cons_zero] at hrunP
    rcases runs_liftGet hrunP with ⟨r', -, hcs, hr'⟩ | hnone
    · simp only [List.cons.injEq, Sigma.mk.injEq, and_true] at hcs
      obtain ⟨-, hy⟩ := hcs
      have hy' : some y = r' := eq_of_heq hy
      subst hy'
      simp only [Option.bind_some] at hr'
      cases y with
      | flat ys =>
        simp only [Adapter.up] at hr'
        cases hl : liftArgs [.u32] ys with
        | none => rw [hl] at hr'; cases hr'
        | some ws' =>
          rw [hl] at hr'
          simp only [Option.map_some, Option.some.injEq, Payload.vals.injEq] at hr'
          subst hr'
          obtain ⟨v, rfl, rfl⟩ := liftArgs_u32 hl
          exact ⟨v, rfl, rfl⟩
      | vals _ => simp [Adapter.up] at hr'
    · cases hnone
  -- the node owning `e`
  have hpok := hok p (List.mem_of_getElem? hpj)
  have hutj : ∀ x ∈ tj, x.2 = InstTests.unitV := fun x hx =>
    hu x (List.mem_flatten.2 ⟨tj, List.mem_of_getElem? htj, hx⟩)
  obtain ⟨x, hk, a, c', ys, hxc, hxe, hlk, hsteps, hst, hys⟩ := node_export hpok hutj hnode
  cases hys
  obtain ⟨xs₀, hxs₀, hF₀⟩ := ends_of_plays hF hok hu
  have hj : j < xs₀.length := by
    have := (List.getElem?_eq_some_iff.1 htj).1
    rw [← hxs₀, List.length_map] at this
    exact this
  refine ⟨xs₀.set j x, ?_, forall₂_set hF₀ hpj hxe, R, e, hR, by simp [hx], ?_⟩
  · rw [List.map_set, hxs₀, hxc]
    obtain ⟨hlt', rfl⟩ := List.getElem?_eq_some_iff.1 htj
    rw [List.set_getElem_self hlt']
  -- the reading's core instance
  intro pre' mi' cargs' post' k base i exps nm cft hfc' hk' hi he
  rw [hfc] at hfc'
  cases hfc'
  obtain ⟨hIlen, A, hAlen, hAin, hLay⟩ := refRead_layout hR hfc
    (fun d hd => postDefOk_not_inline (List.all_eq_true.1 hpostOk d hd))
  obtain ⟨j', p', rfl, hpj', hexps, rfl⟩ := node_of_layout hAin hLay hN' hk'
  rw [← hIm'] at he
  have hilt : i < exps.length := (List.getElem?_eq_some_iff.1 hi).1
  have hjj := node_unique hpj hpj' hle hlt (by omega) (by rw [hexps]; omega)
  subst hjj
  rw [hpj] at hpj'
  cases hpj'
  have hi' : e - (hostI.length + coreWidth (ps.take j)) = i := by omega
  have hnm : ((CoreModule.exports p.1)[e - (hostI.length + coreWidth (ps.take j))]'hk).1 = nm := by
    have h1 : (CoreModule.exports p.1)[e - (hostI.length + coreWidth (ps.take j))]? =
        some (nm, cft) := by rw [hi', hexps]; exact hi
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at h1
    rw [h1]
  rw [hnm] at hlk
  exact ⟨j, x, a, c', v, by rw [hAlen], List.getElem?_set_self hj, hlk, hsteps, hst, rfl⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
