module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapStep
public import Silmaril.Proofs.Wasm.Component.Reference.SplitBack
public import Silmaril.Proofs.Wasm.Component.Reference.StartBase
public import Silmaril.Proofs.Wasm.Component.Reference.LinkExp
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.CoreSim
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.HostCode

/-!
# Threads in the shared store, imports kept in place

The thread-level counterpart of `Multi.GapStep`: a thread `t` of the store `s` alone and a thread
`tR` of the shared store `g.rel s` are related when `tR`'s configuration is the map of `t`'s
(`gC g`). Along that relation:

* `invoke_gap`: the invocation of the mapped function is the map of the invocation;
* `decompose?_gap`: a host-call redex is mapped to a host-call redex of the same host function
  (the callee at the mapped address), with mapped context and arguments; `status_gap_callout`,
  `status_gap_values`: the statuses of a callout and of a return are mapped;
* `resume_gap`: resuming after a callout commutes with the map, and keeps the thread good;
* `internal_gap`: an internal run of `t` is an internal run of `tR`, keeping the relation, the
  split invariant (`Reference.SplitGood`) and the functions of the store.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Component.Reference (CMap SplitGood)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore (steps_of_internal internal_of_steps)
open Silmaril.Wasm.SingleThreaded (Ctx GrowOracle Internal status decompose? resume)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {H : Type}

/-! ## The map of code as a code map -/

namespace GShift

variable (δ : GShift)

/-- The map as a `Reference.CMap` (a map of references and one of frames). -/
def cmap : CMap := ⟨δ.ref, δ.frame⟩

theorem code_eq_cmap : ∀ l : List Admin, δ.code l = δ.cmap.code l
  | [] => by simp
  | .label n c b :: l => by simp [code_eq_cmap b, code_eq_cmap l]
  | .handler n cs b :: l => by simp [code_eq_cmap b, code_eq_cmap l]
  | .frame n f b :: l => by simp [code_eq_cmap b, code_eq_cmap l]; rfl
  | .ref r :: l => by simp [code_eq_cmap l]; rfl
  | .plain i :: l => by simp [code_eq_cmap l]
  | .callRefType d :: l => by simp [code_eq_cmap l]
  | .returnCallRefType d :: l => by simp [code_eq_cmap l]
  | .trap :: l => by simp [code_eq_cmap l]

theorem val_eq_cmap (v : Val) : δ.val v = δ.cmap.val v := by
  cases v <;> rfl

end GShift

/-! ## Invocations and callouts -/

section Callout

variable (g : Gap H)

/-- **The invocation of the mapped function is the map of the invocation.** -/
theorem invoke_gap {u : Store H} (hP : g.PreOk u.funcs) (a : Nat) :
    invoke (g.rel u) (g.sh.fn a) [] = gC g (invoke u a []) := by
  have hf := funcs_gap g hP a
  simp only [gC, invoke, hf, Option.map_map, vals, List.map_nil, List.nil_append]
  simp only [GShift.code, GShift.ref, Function.comp_def, GShift.finst]
  rfl

/-- **A host-call redex in the shared store**: the callee at the mapped address, the same host
function, mapped context and arguments. -/
theorem decompose?_gap {s : Store H} (hP : g.PreOk s.funcs) {X : List Admin} {E : Ctx} {a : Nat}
    {h : H} {args : List Val} (hd : decompose? s X = some (E, a, h, args)) :
    decompose? (g.rel s) (g.sh.code X) =
      some (g.sh.cmap.ctx E, g.sh.fn a, h, args.map g.sh.val) := by
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, rfl⟩ :=
    Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  have hf' := funcs_gap_of g hP hf
  have hfill : g.sh.code (E.fill (vals args ++ [.ref (.func a), yy])) =
      (g.sh.cmap.ctx E).fill (vals (args.map g.sh.val) ++ [.ref (.func (g.sh.fn a)), yy]) := by
    rw [GShift.code_eq_cmap, CMap.code_fill, CMap.code_append, CMap.code_vals, CMap.code_ref,
      CMap.code_callRef _ hyy, CMap.code_nil]
    have : (fun v => g.sh.cmap.val v) = g.sh.val := funext fun v => (GShift.val_eq_cmap _ v).symm
    simp only [this]
    rfl
  rw [hfill]
  exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ hyy hf' he (by simpa using hn) hcode

/-- The mapped code is values only if the code is. -/
theorem code_gap_vals {X : List Admin} {vs : List Val} (h : g.sh.code X = vals vs) :
    ∃ ws, X = vals ws := by
  rw [GShift.code_eq_cmap] at h
  obtain ⟨ws, rfl, -⟩ := CMap.code_eq_vals h
  exact ⟨ws, rfl⟩

/-- **The status of a callout, in the shared store.** -/
theorem status_gap_callout {o : GrowOracle} {s : Store H} (hP : g.PreOk s.funcs) {t tR : STh}
    (hth : tR.config (g.rel s) = gC g (t.config s)) {h : H} {args : List Val}
    (hst : status o s t = .callout h args) :
    status o (g.rel s) tR = .callout h (args.map g.sh.val) ∧
      ∃ E a, decompose? s (t.config s).code = some (E, a, h, args) ∧
        decompose? (g.rel s) (tR.config (g.rel s)).code =
          some (g.sh.cmap.ctx E, g.sh.fn a, h, args.map g.sh.val) := by
  obtain ⟨E, a, hd⟩ := Silmaril.Wasm.SingleThreaded.status_callout_inv hst
  have hd' : decompose? (g.rel s) (tR.config (g.rel s)).code =
      some (g.sh.cmap.ctx E, g.sh.fn a, h, args.map g.sh.val) := by
    rw [hth]
    exact decompose?_gap g hP hd
  refine ⟨Silmaril.Wasm.SingleThreaded.status_callout_of ?_ ?_ ?_ hd', E, a, hd, hd'⟩
  · intro vs hv
    rw [hv, Silmaril.Wasm.SingleThreaded.decompose?_vals_nil] at hd'
    cases hd'
  · intro hv
    rw [hv, Silmaril.Proofs.Wasm.Component.Reference.decompose?_trap] at hd'
    cases hd'
  · intro b hv
    rw [hv, Silmaril.Proofs.Wasm.Component.Reference.decompose?_throwing'] at hd'
    cases hd'

/-- **The status of a return of values, in the shared store.** -/
theorem status_gap_values {o : GrowOracle} {s : Store H} {t tR : STh}
    (hth : tR.config (g.rel s) = gC g (t.config s)) {vs : List Val}
    (hst : status o s t = .returned (.values vs)) :
    status o (g.rel s) tR = .returned (.values (vs.map g.sh.val)) := by
  have hc := Silmaril.Wasm.SingleThreaded.status_returned_values hst
  have hc' : (tR.config (g.rel s)).code = vals (vs.map g.sh.val) := by
    rw [hth]
    show g.sh.code (t.config s).code = _
    rw [hc, GShift.code_vals]
  have hex : ∃ ws, (tR.config (g.rel s)).code = vals ws := ⟨_, hc'⟩
  unfold status
  dsimp only
  rw [dite_eq_left hex, Silmaril.Wasm.SingleThreaded.vals_injective (hex.choose_spec.symm.trans hc')]

/-- **Resuming after a callout commutes with the map.** -/
theorem resume_gap {s : Store H} {t tR : STh} (hth : tR.config (g.rel s) = gC g (t.config s))
    {E : Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, h, args))
    (hd' : decompose? (g.rel s) (tR.config (g.rel s)).code =
      some (g.sh.cmap.ctx E, g.sh.fn a, h, args.map g.sh.val)) :
    (resume (g.rel s) tR (.values [])).config (g.rel s) =
      gC g ((resume s t (.values [])).config s) := by
  unfold resume
  simp only [hd, hd']
  show (⟨g.rel s, (tR.config (g.rel s)).frame, (g.sh.cmap.ctx E).fill _⟩ : Config H) =
    ⟨g.rel s, g.sh.frame (t.config s).frame, g.sh.code (E.fill _)⟩
  rw [hth, GShift.code_eq_cmap, CMap.code_fill]
  simp [Silmaril.Wasm.SingleThreaded.CallResult.toAdmin, gC]

/-- **Resuming a good thread after a callout with no values keeps it good.** -/
theorem splitGood_resume {s : Store H} {t : STh} (hg : SplitGood (t.config s)) {E : Ctx} {a : Nat}
    {h : H} {args : List Val} (hd : decompose? s (t.config s).code = some (E, a, h, args)) :
    SplitGood ((resume s t (.values [])).config s) := by
  obtain ⟨ρ, O, σ, hR, hf, hc⟩ := hg
  obtain ⟨-, yy, -, -, -, -, -, -, -, hX⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  unfold resume
  simp only [hd]
  refine ⟨ρ, O, σ, ?_, hf, ?_⟩
  · simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hR
  · refine Own.CodeGood.fill E (xs := vals args ++ [.ref (.func a), yy]) ?_ ?_
    · rw [← hX]; exact hc
    · simpa [Silmaril.Wasm.SingleThreaded.CallResult.toAdmin] using O.codeGood_nil

end Callout

/-! ## Internal runs -/

section Runs

variable (g : Gap H) {o : GrowOracle}

/-- **An internal run, in the shared store**: an internal run of a good thread `t` from `s` is an
internal run of the related thread `tR` from `g.rel s`, to a related thread; the end is good and
the functions of the store are kept. -/
theorem internal_gap {s s₁ : Store H} {t t₁ tR : STh}
    (hrun : Relation.ReflTransGen (Internal o) (s, t) (s₁, t₁)) (hg : SplitGood (t.config s))
    (hP : g.PreOk s.funcs) (hinj : Function.Injective g.sh.fn)
    (hth : tR.config (g.rel s) = gC g (t.config s)) :
    ∃ tR', Relation.ReflTransGen (Internal o) (g.rel s, tR) (g.rel s₁, tR') ∧
      tR'.config (g.rel s₁) = gC g (t₁.config s₁) ∧ SplitGood (t₁.config s₁) ∧
      s₁.funcs = s.funcs := by
  have h₁ := steps_of_internal hrun
  have hP' : g.PreOk (t.config s).store.funcs := by
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]; exact hP
  obtain ⟨h₂, hg₁, hfs⟩ := steps_gap g h₁ hg hP' hinj
  rw [← hth] at h₂
  obtain ⟨tR', hr, ht'⟩ := internal_of_steps h₂
  have hst : (gC g (t₁.config s₁)).store = g.rel s₁ := by
    show g.rel (t₁.config s₁).store = _
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]
  rw [hst] at hr ht'
  refine ⟨tR', hr, ht', hg₁, ?_⟩
  simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using hfs

end Runs

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
