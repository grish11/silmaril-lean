module

public import Silmaril.Wasm.Component.Reference.LinkedGLink.Defs
public import Silmaril.Wasm.Abstract.NodeTrap.Thms
public import Silmaril.Wasm.Component.ABI.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# The importer's session triple: paths, call prefixes and traps (proofs)

* Paths of the importer's core instance: concatenation and splitting (`path_append`,
  `path_split`); a round stays at its export question (`path_running`); chains of single calls
  (`path_chain`).
* **Traps.** By `NodeTrap.instTripleS_trapAbortsRound` (the instance triple of a Core 3.0
  instance aborts its round at an import trap), an importer round makes no call after a core call
  answered by a trap (`no_call_after_trap`), returns the trap after it (`fin_after_trap`) and does
  not diverge host-free after it (`div_after_trap`).
* **Call prefixes.** A wired log of `ImpRel`-related calls splits at any of its calls
  (`wireLog_split`); every call prefix forced by the triple is a pending call
  (`satP_impTripleS_subset`).
* `impTripleS_trapAbortsRound`, `noPlainTrap_impTripleS`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance Answer)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Abstract.NodeTrap (IsTrapA instTripleS_trapAbortsRound)
open Silmaril.Wasm.Abstract.InstSession (instTripleS sAns)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {I : ScalarInstance} {P : Profile}

/-! ## Paths -/

theorem path_append {x y z : I.HState} {l₁ l₂ : List (Move I.E I.F)} (h₁ : I.Path P x l₁ y)
    (h₂ : I.Path P y l₂ z) : I.Path P x (l₁ ++ l₂) z := by
  induction h₁ with
  | nil => simpa using h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem path_split {x z : I.HState} {l₁ l₂ : List (Move I.E I.F)}
    (h : I.Path P x (l₁ ++ l₂) z) : ∃ y, I.Path P x l₁ y ∧ I.Path P y l₂ z := by
  induction l₁ generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons m l ih =>
    rw [List.cons_append] at h
    cases h with
    | cons ht hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons ht h₁, h₂⟩

theorem callMoves_append {E F : Sig.{0}} (l₁ l₂ : List (Σ m : E.Op, E.Ar m)) :
    (callMoves (l₁ ++ l₂) : List (Move E F)) = callMoves l₁ ++ callMoves l₂ := by
  induction l₁ with
  | nil => rfl
  | cons x l ih => obtain ⟨m, n⟩ := x; simp [callMoves, ih]

theorem callMoves_eq {E F : Sig.{0}} (l : List (Σ m : E.Op, E.Ar m)) :
    (callMoves l : List (Move E F)) = StratObs.callMoves l := by
  induction l with
  | nil => rfl
  | cons x l ih => obtain ⟨m, n⟩ := x; simp [callMoves, StratObs.callMoves, ih]

/-- From a running state, a path of answered calls stays running at the same question. -/
theorem path_running {f : I.F.Op} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {cs : List (Σ e : I.E.Op, I.E.Ar e)} {x : I.HState}
    (h : I.Path P (.running f s t) (callMoves cs) x) : ∃ s' t', x = .running f s' t' := by
  induction cs generalizing s t with
  | nil => cases h; exact ⟨s, t, rfl⟩
  | cons c cs ih =>
    obtain ⟨m, n⟩ := c
    cases h with
    | cons h₁ h =>
      cases h₁ with
      | ucall _ _ _ =>
        cases h with
        | cons h₂ h =>
          cases h₂ with
          | uret v => exact ih h

/-- A round prefix ends running at its question. -/
theorem path_idle_running {f : I.F.Op} {u : Store Nat} {cs : List (Σ e : I.E.Op, I.E.Ar e)}
    {x : I.HState} (h : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs) x) :
    ∃ s t, x = .running f s t := by
  cases h with
  | cons h₁ h => cases h₁ with | call => exact path_running h

/-- The first call of a list of calls, from a running state. -/
theorem path_first_call {f : I.F.Op} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {c : Σ e : I.E.Op, I.E.Ar e} {rest : List (Move I.E I.F)} {x : I.HState}
    (h : I.Path P (.running f s t) (callMoves [c] ++ rest) x) :
    ∃ s' t', I.Path P (.running f s t) [.inl (.ask c.1)] (.waiting f s' t' c.1) := by
  obtain ⟨m, n⟩ := c
  cases h with
  | cons h₁ _ =>
    cases h₁ with
    | ucall run callout op => exact ⟨_, _, .cons (.ucall run callout op) (.nil _)⟩

/-- A chain of single calls after a round prefix. -/
theorem path_chain {f : I.F.Op} {u : Store Nat} {cs : List (Σ e : I.E.Op, I.E.Ar e)}
    {r : ℕ → I.HState} {c : ℕ → Σ e : I.E.Op, I.E.Ar e}
    (h₀ : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (r 0))
    (hr : ∀ k, I.Path P (r k) (callMoves [c k]) (r (k + 1))) (n : ℕ) :
    I.Path P (.idle u) (.inr (.ask f) :: callMoves (cs ++ List.ofFn fun i : Fin n => c i))
      (r n) := by
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    rw [List.ofFn_succ_last, ← List.append_assoc, callMoves_append, ← List.cons_append]
    exact path_append ih (by simpa using hr n)

/-! ## Traps -/

theorem sigma_trap {x : Σ e : I.E.Op, I.E.Ar e} (h : x.2 = Answer.trap) :
    x = ⟨x.1, Answer.trap⟩ := by
  obtain ⟨e, v⟩ := x; exact Sigma.ext rfl (heq_of_eq h)

/-- **No call after a trapped call.** -/
theorem no_call_after_trap {u : Store Nat} {f : I.F.Op} {c d : List (Σ e : I.E.Op, I.E.Ar e)}
    {m : I.E.Op} {m' : I.E.Op} {x : I.HState}
    (h : I.Path P (.idle u)
      (.inr (.ask f) :: callMoves (c ++ ⟨m, Answer.trap⟩ :: d) ++ [.inl (.ask m')]) x) : False := by
  refine (instTripleS_trapAbortsRound (I := I) (P := P)).pend u f c m Answer.trap d m' rfl ⟨x, ?_⟩
  simpa [callMoves_eq] using h

/-- **A returning round after a trapped call** returns the trap at once. -/
theorem fin_after_trap {u u₁ : Store Nat} {f : I.F.Op} {c d : List (Σ e : I.E.Op, I.E.Ar e)}
    {m : I.E.Op} {w : I.F.Ar f}
    (h : I.Path P (.idle u)
      (.inr (.ask f) :: callMoves (c ++ ⟨m, Answer.trap⟩ :: d) ++ [.inr (.ans f w)]) (.idle u₁)) :
    d = [] ∧ w = Answer.trap := by
  have hm : (c ++ ⟨m, Answer.trap⟩ :: d, End.ret (sAns f w) u₁) ∈ (instTripleS I P).1 u f :=
    .inl ⟨w, u₁, rfl, by simpa [callMoves_eq] using h⟩
  obtain ⟨hd, he⟩ := (instTripleS_trapAbortsRound (I := I) (P := P)).beh u f c m Answer.trap d _ rfl hm
  refine ⟨hd, ?_⟩
  revert he
  cases w <;> simp [sAns, TrapEnd]

/-- **No host-free divergence after a trapped call.** -/
theorem div_after_trap {u s : Store Nat} {f : I.F.Op} {c d : List (Σ e : I.E.Op, I.E.Ar e)}
    {m : I.E.Op} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : I.Path P (.idle u) (.inr (.ask f) :: callMoves (c ++ ⟨m, Answer.trap⟩ :: d))
      (.running f s t)) (hd : Linked2.DivB P s t) : False := by
  have hm : (c ++ ⟨m, Answer.trap⟩ :: d, End.div) ∈ (instTripleS I P).1 u f :=
    .inr ⟨rfl, s, t, by simpa [callMoves_eq] using h, hd⟩
  exact ((instTripleS_trapAbortsRound (I := I) (P := P)).beh u f c m Answer.trap d _ rfl hm).2

/-- A trapped call inside a round prefix followed by one more call is impossible. -/
theorem chain_trap_false {f : I.F.Op} {u : Store Nat} {cs : List (Σ e : I.E.Op, I.E.Ar e)}
    {r : ℕ → I.HState} {c : ℕ → Σ e : I.E.Op, I.E.Ar e}
    (h₀ : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (r 0))
    (hr : ∀ k, I.Path P (r k) (callMoves [c k]) (r (k + 1))) (n : ℕ)
    (ht : (c n).2 = Answer.trap) : False := by
  have h := path_chain h₀ hr (n + 1)
  obtain ⟨s, t, hrs⟩ := path_idle_running h
  have h' := hr (n + 1)
  rw [hrs] at h'
  obtain ⟨s', t', hc⟩ := path_first_call (rest := []) (by simpa using h')
  rw [← hrs] at hc
  have := path_append h hc
  have e : (List.ofFn fun i : Fin (n + 1) => c i) =
      (List.ofFn fun i : Fin n => c i) ++ [⟨(c n).1, Answer.trap⟩] := by
    rw [List.ofFn_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← sigma_trap ht]
  rw [e] at this
  exact no_call_after_trap (c := cs ++ List.ofFn fun i : Fin n => c i) (d := [])
    (by simpa using this)

/-- A trapped call inside a round prefix after which the round calls again is impossible. -/
theorem prefix_trap_false {f : I.F.Op} {u : Store Nat} {c₁ c₂ : List (Σ e : I.E.Op, I.E.Ar e)}
    {m : I.E.Op} {x y : I.HState} {c : Σ e : I.E.Op, I.E.Ar e}
    (h₀ : I.Path P (.idle u) (.inr (.ask f) :: callMoves (c₁ ++ ⟨m, Answer.trap⟩ :: c₂)) x)
    (h₁ : I.Path P x (callMoves [c]) y) : False := by
  obtain ⟨s, t, rfl⟩ := path_idle_running h₀
  obtain ⟨s', t', hc⟩ := path_first_call (rest := []) (by simpa using h₁)
  exact no_call_after_trap (path_append h₀ hc)

/-! ## `ImpRel` -/

variable {b : SimpleI} {wire : List Nat}

/-- **The shape of `ImpRel`**: no component call and a core trap, or one component call on the
lifted arguments. -/
theorem impRel_cases {x : Σ e : I.E.Op, I.E.Ar e} {ds : List b.ICall} (h : ImpRel b I x ds) :
    (ds = [] ∧ x.2 = Answer.trap) ∨
      ∃ (nm : String) (ft : FuncTy) (ws : List IVal) (hk : x.1.1.val < b.imports.length)
        (R : Option Payload), b.imports[x.1.1.val]? = some (nm, ft) ∧
        liftArgs ft.params (x.1.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws ∧
        ds = [⟨(⟨x.1.1.val, hk⟩, .vals ws), R⟩] ∧
        x.2 = payloadAnswer (I.imports.get x.1.1) (R.bind (Adapter.lower ft).up) := by
  obtain ⟨nm, ft, A, h₁, h₂, h₃⟩ := h
  split at h₃
  · obtain ⟨rfl, rfl⟩ := h₃
    exact .inl ⟨rfl, by rw [← h₂]; rfl⟩
  · rename_i ws hl
    obtain ⟨hk, R, rfl, rfl⟩ := h₃
    exact .inr ⟨nm, ft, ws, hk, R, h₁, hl, rfl, h₂.symm⟩

theorem impRel_len {x : Σ e : I.E.Op, I.E.Ar e} {ds : List b.ICall} (h : ImpRel b I x ds) :
    ds = [] ∨ ∃ z, ds = [z] := by
  rcases impRel_cases h with ⟨rfl, -⟩ | ⟨_, _, _, _, _, -, -, rfl, -⟩
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

/-- A component call answered by a trap comes from a core call answered by a trap. -/
theorem impRel_trap {x : Σ e : I.E.Op, I.E.Ar e} {z : b.ICall} (h : ImpRel b I x [z])
    (hz : z.2 = none) : x.2 = Answer.trap := by
  rcases impRel_cases h with ⟨h, -⟩ | ⟨_, _, _, _, R, -, -, h, hx⟩
  · cases h
  · simp only [List.cons.injEq, and_true] at h
    subst h
    rw [hx, show R = none from hz]
    rfl

theorem sumAns_inj {R R' : Option Payload} (h : ExpSpec.sumAns R = ExpSpec.sumAns R') :
    R = R' := by
  cases R <;> cases R' <;> simp_all [ExpSpec.sumAns]

theorem sumAns_eq_inr {R : Option Payload} (h : ExpSpec.sumAns R = .inr PUnit.unit) : R = none :=
  sumAns_inj (R' := none) h

theorem lowered_forall₂ {j : Fin b.exports.length} {vs : List IVal} {f : I.F.Op}
    {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    (h : b.Lowered I j vs f cs dss) : List.Forall₂ (ImpRel b I) cs dss := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h

theorem wireCall_snd {z : b.ICall} {m : sigS.Op} {n : sigS.Ar m}
    (hz : b.wireCall wire z = ⟨m, n⟩) : ExpSpec.sumAns z.2 = n := by
  unfold SimpleI.wireCall at hz
  simp only [Sigma.mk.injEq] at hz
  exact eq_of_heq hz.2

/-! ## Splitting wired logs -/

theorem wireLog_append (l₁ l₂ : List b.ICall) :
    b.wireLog wire (l₁ ++ l₂) = b.wireLog wire l₁ ++ b.wireLog wire l₂ := by
  simp [SimpleI.wireLog]

/-- **A wired log splits at any of its calls**, at one `ImpRel`-related core call. -/
theorem wireLog_split {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    (h : List.Forall₂ (ImpRel b I) cs dss) {c d : List (Call sigS)} {m : sigS.Op}
    {n : sigS.Ar m} (he : b.wireLog wire dss.flatten = c ++ ⟨m, n⟩ :: d) :
    ∃ cs₁ x cs₂ dss₁ z dss₂, cs = cs₁ ++ x :: cs₂ ∧ dss = dss₁ ++ [z] :: dss₂ ∧
      List.Forall₂ (ImpRel b I) cs₁ dss₁ ∧ ImpRel b I x [z] ∧
      List.Forall₂ (ImpRel b I) cs₂ dss₂ ∧ c = b.wireLog wire dss₁.flatten ∧
      b.wireCall wire z = ⟨m, n⟩ ∧ d = b.wireLog wire dss₂.flatten := by
  induction h generalizing c with
  | nil => simp [SimpleI.wireLog] at he
  | @cons x ds cs dss hx hrest ih =>
    rcases impRel_len hx with rfl | ⟨z, rfl⟩
    · obtain ⟨cs₁, x', cs₂, dss₁, z, dss₂, rfl, rfl, h₁, hx', h₂, rfl, hz, rfl⟩ :=
        ih (by simpa using he)
      exact ⟨x :: cs₁, x', cs₂, [] :: dss₁, z, dss₂, rfl, rfl, .cons hx h₁, hx', h₂, by simp,
        hz, rfl⟩
    · simp only [List.flatten_cons, List.singleton_append, SimpleI.wireLog, List.map_cons] at he
      cases c with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        exact ⟨[], x, cs, [], z, dss, rfl, rfl, .nil, hx, hrest, rfl, he.1, he.2.symm⟩
      | cons c₀ c =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨cs₁, x', cs₂, dss₁, z', dss₂, rfl, rfl, h₁, hx', h₂, rfl, hz, rfl⟩ := ih he.2
        exact ⟨x :: cs₁, x', cs₂, [z] :: dss₁, z', dss₂, rfl, rfl, .cons hx h₁, hx', h₂,
          by simp [SimpleI.wireLog, he.1], hz, rfl⟩

/-! ## Pending calls -/

theorem lowered_append {j : Fin b.exports.length} {vs : List IVal} {f : I.F.Op}
    {cs cs' : List (Σ e : I.E.Op, I.E.Ar e)} {dss dss' : List (List b.ICall)}
    (h : b.Lowered I j vs f cs dss) (h' : List.Forall₂ (ImpRel b I) cs' dss') :
    b.Lowered I j vs f (cs ++ cs') (dss ++ dss') := by
  obtain ⟨xs, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨xs, h₁, h₂, h₃, List.rel_append h₄ h'⟩

theorem lowered_prefix {j : Fin b.exports.length} {vs : List IVal} {f : I.F.Op}
    {cs cs' : List (Σ e : I.E.Op, I.E.Ar e)} {dss dss' : List (List b.ICall)}
    (h : b.Lowered I j vs f (cs ++ cs') (dss ++ dss'))
    (h' : List.Forall₂ (ImpRel b I) cs dss) : b.Lowered I j vs f cs dss := by
  obtain ⟨xs, h₁, h₂, h₃, -⟩ := h
  exact ⟨xs, h₁, h₂, h₃, h'⟩

/-- **A pending call** from a round prefix followed by the call out of one more related call. -/
theorem mem_impPend_of {u : Store Nat} {j : Fin b.exports.length} {vs : List IVal}
    {f : I.F.Op} {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    {x : Σ e : I.E.Op, I.E.Ar e} {z : b.ICall} {y : I.HState} (hlow : b.Lowered I j vs f cs dss)
    (hx : ImpRel b I x [z])
    (hp : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs ++ [.inl (.ask x.1)]) y) :
    (b.wireLog wire dss.flatten, (b.wireCall wire z).1) ∈
      b.impPend P wire I u (j.val, .vals vs) := by
  obtain ⟨y₀, hp₀, hp₁⟩ := path_split hp
  obtain ⟨s, t, rfl⟩ := path_idle_running hp₀
  cases hp₁ with
  | cons h₁ h₂ =>
    cases h₂
    cases h₁ with
    | ucall run callout op =>
      rcases impRel_cases hx with ⟨h, -⟩ | ⟨nm, ft, ws, hk, R, himp, hl, hz, -⟩
      · cases h
      · simp only [List.cons.injEq, and_true] at hz
        subst hz
        exact ⟨j, vs, f, cs, dss, s, t, x.1, _, _, nm, ft, ws, rfl, hlow, hp₀,
          .cons (.ucall run callout op) (.nil _), himp, hl, rfl⟩

/-- A round path over the calls `cs`, cut at a call of `cs`. -/
theorem path_cut {u : Store Nat} {f : I.F.Op} {cs₁ cs₂ : List (Σ e : I.E.Op, I.E.Ar e)}
    {x : Σ e : I.E.Op, I.E.Ar e} {rest : List (Move I.E I.F)} {y : I.HState}
    (h : I.Path P (.idle u) (.inr (.ask f) :: callMoves (cs₁ ++ x :: cs₂) ++ rest) y) :
    ∃ y', I.Path P (.idle u) (.inr (.ask f) :: callMoves cs₁ ++ [.inl (.ask x.1)]) y' := by
  obtain ⟨m, n⟩ := x
  obtain ⟨y₁, h, -⟩ := path_split h
  rw [callMoves_append, ← List.cons_append] at h
  obtain ⟨y₂, h₁, h₂⟩ := path_split h
  have h₂' : I.Path P y₂ (.inl (.ask m) :: .inl (.ans m n) :: callMoves cs₂) y₁ := h₂
  cases h₂' with
  | cons t₁ _ => exact ⟨_, path_append h₁ (.cons t₁ (.nil _))⟩

/-- A call prefix of a wired log of a round prefix is a pending call. -/
theorem mem_impPend_of_callPre {u : Store Nat} {j : Fin b.exports.length} {vs : List IVal}
    {f : I.F.Op} {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    {rest : List (Move I.E I.F)} {y : I.HState} (hlow : b.Lowered I j vs f cs dss)
    (hp : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs ++ rest) y)
    {c : List (Call sigS)} {m : sigS.Op} (hc : StratObs.CallPre c m (b.wireLog wire dss.flatten)) :
    (c, m) ∈ b.impPend P wire I u (j.val, .vals vs) := by
  obtain ⟨n, d, hd⟩ := hc
  obtain ⟨cs₁, x, cs₂, dss₁, z, dss₂, rfl, rfl, h₁, hx, -, rfl, hz, -⟩ :=
    wireLog_split (lowered_forall₂ hlow) hd
  obtain ⟨y', hy'⟩ := path_cut hp
  have := mem_impPend_of (wire := wire) (lowered_prefix hlow h₁) hx hy'
  rwa [hz] at this

theorem streamTake_streamAppend {α : Type} (l : List α) (ω : ℕ → α) (n : ℕ) :
    streamTake (Shape.streamAppend l ω) (l.length + n) = l ++ streamTake ω n := by
  apply List.ext_getElem
  · simp [streamTake]
  · intro i h₁ h₂
    simp only [streamTake, List.getElem_ofFn, List.getElem_append]
    by_cases h : i < l.length
    · simp [h, Shape.streamAppend_lt h]
    · simp [h, Shape.streamAppend_ge (not_lt.1 h)]

theorem streamTake_streamAppend_lt {α : Type} (l : List α) (ω : ℕ → α) {k : ℕ}
    (hk : k ≤ l.length) : streamTake (Shape.streamAppend l ω) k = l.take k := by
  apply List.ext_getElem
  · simp [streamTake]; omega
  · intro i h₁ h₂
    simp only [streamTake, List.length_ofFn] at h₁
    simp only [streamTake, List.getElem_ofFn, List.getElem_take]
    exact Shape.streamAppend_lt (by omega)

theorem flatten_ofFn_singleton {α : Type} {n : ℕ} (f : Fin n → α) :
    (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ, ih]

theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {n : ℕ} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ i, R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih => rw [List.ofFn_succ, List.ofFn_succ]; exact .cons (h 0) (ih fun i => h i.succ)

/-- A wired log cut at position `k` of a stream starting with it. -/
theorem streamAppend_split {L : List (Call sigS)} {Y : ℕ → Call sigS} {k : ℕ}
    (hk : k < L.length) :
    L = streamTake (Shape.streamAppend L Y) k ++
      ⟨(Shape.streamAppend L Y k).1, (Shape.streamAppend L Y k).2⟩ :: L.drop (k + 1) := by
  rw [streamTake_streamAppend_lt _ _ hk.le, Shape.streamAppend_lt hk]
  show L = L.take k ++ L[k] :: L.drop (k + 1)
  rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]


/-- **The triple is saturated**: every call prefix it forces is a pending call. -/
theorem satP_impTripleS_subset (u : Store Nat) (q : Nat × Payload) :
    StratObs.satP (b.impTripleS P wire I) u q ⊆ b.impPend P wire I u q := by
  rintro ⟨c, m⟩ (hx | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, hk, hm⟩)
  · exact hx
  · obtain ⟨j, vs, f, cs, dss, s, t, e, s', t', nm, ft, ws, rfl, hlow, hp, hpe, -, -, hx⟩ := hd
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact mem_impPend_of_callPre (rest := []) hlow (by simpa using hp) hc
  · rcases hd with ⟨-, hd⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, hlog, hd⟩
    · simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      obtain ⟨n, d, hd⟩ := hc
      simp at hd
    · simp only at hlog
      subst hlog
      rcases hd with ⟨w, u₁, hp, -⟩ | ⟨s, t, hp, -, -⟩
      · exact mem_impPend_of_callPre hlow hp hc
      · exact mem_impPend_of_callPre (rest := []) hlow (by simpa using hp) hc
  · obtain ⟨j, vs, f, cs, dss, s, t, r, cc, y, rfl, hlow, hp, hr0, hall, rfl⟩ := hω
    simp only at hk hm
    subst hk hm
    rw [← hr0] at hp
    by_cases hkl : k < (b.wireLog wire dss.flatten).length
    · exact mem_impPend_of_callPre (rest := []) hlow (by simpa using hp)
        ⟨_, _, streamAppend_split hkl⟩
    · obtain ⟨n, rfl⟩ : ∃ n, k = (b.wireLog wire dss.flatten).length + n :=
        ⟨k - (b.wireLog wire dss.flatten).length, by omega⟩
      have hch := path_chain hp (fun k => (hall k).1) n
      obtain ⟨s₁, t₁, hrs⟩ := path_idle_running hch
      have h' := (hall n).1
      rw [hrs] at h'
      obtain ⟨s', t', hc⟩ := path_first_call (rest := []) (by simpa using h')
      rw [← hrs] at hc
      have hlow' := lowered_append hlow (cs' := List.ofFn fun i : Fin n => cc i)
        (dss' := List.ofFn fun i : Fin n => [y i]) (forall₂_ofFn fun i => (hall i).2)
      have := mem_impPend_of (wire := wire) hlow' (hall n).2 (path_append hch hc)
      have hm : (Shape.streamAppend (b.wireLog wire dss.flatten) (fun k => b.wireCall wire (y k))
          ((b.wireLog wire dss.flatten).length + n)) = b.wireCall wire (y n) := by
        rw [Shape.streamAppend_ge (by omega)]
        simp
      have key : streamTake (Shape.streamAppend (b.wireLog wire dss.flatten)
            (fun k => b.wireCall wire (y k))) ((b.wireLog wire dss.flatten).length + n) =
          b.wireLog wire (dss ++ List.ofFn fun i : Fin n => [y i]).flatten := by
        rw [streamTake_streamAppend, List.flatten_append, flatten_ofFn_singleton, wireLog_append]
        simp [SimpleI.wireLog, streamTake, List.map_ofFn, Function.comp_def]
      rw [key, hm]
      exact this

/-! ## Traps of the importer's triple -/

/-- **Every round of the importer aborts at a trapped wired call.** -/
theorem impTripleS_trapAbortsRound : TrapAbortsRound IsTrapS (b.impTripleS P wire I) where
  beh := by
    intro u q c m n d e hn hx
    rcases hx with ⟨-, hx⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, hlog, hd⟩
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨h, -⟩ := hx
      simp at h
    · simp only at hlog
      obtain ⟨cs₁, x, cs₂, dss₁, z, dss₂, rfl, rfl, -, hx, h₂, -, hz, rfl⟩ :=
        wireLog_split (lowered_forall₂ hlow) hlog.symm
      have hz2 : z.2 = none := sumAns_eq_inr ((wireCall_snd hz).trans hn)
      have hxt := impRel_trap hx hz2
      rw [sigma_trap hxt] at hd
      rcases hd with ⟨w, u₁, hp, rfl⟩ | ⟨s, t, hp, hB, -⟩
      · obtain ⟨rfl, rfl⟩ := fin_after_trap hp
        cases h₂
        exact ⟨rfl, by simp [SimpleI.liftAns, answerPayload, ExpSpec.sumAns, TrapEnd]⟩
      · exact (div_after_trap hp hB).elim
  pend := by
    intro u q c m n d m' hn hx
    obtain ⟨j, vs, f, cs, dss, s, t, e, s', t', nm, ft, ws, rfl, hlow, hp, hpe, -, -, hx⟩ := hx
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hlog, -⟩ := hx
    obtain ⟨cs₁, x, cs₂, dss₁, z, dss₂, rfl, rfl, -, hx, -, -, hz, -⟩ :=
      wireLog_split (lowered_forall₂ hlow) hlog.symm
    have hz2 : z.2 = none := sumAns_eq_inr ((wireCall_snd hz).trans hn)
    rw [sigma_trap (impRel_trap hx hz2)] at hp
    exact no_call_after_trap (path_append hp hpe)
  inf := by
    intro u q ω hω k hk
    obtain ⟨j, vs, f, cs, dss, s, t, r, cc, y, rfl, hlow, hp, hr0, hall, rfl⟩ := hω
    rw [← hr0] at hp
    by_cases hkl : k < (b.wireLog wire dss.flatten).length
    · obtain ⟨cs₁, x, cs₂, dss₁, z, dss₂, rfl, rfl, -, hx, -, -, hz, -⟩ :=
        wireLog_split (lowered_forall₂ hlow) (streamAppend_split (Y := fun k => b.wireCall wire (y k)) hkl)
      have hz2 : z.2 = none := sumAns_eq_inr ((wireCall_snd hz).trans hk)
      rw [sigma_trap (impRel_trap hx hz2)] at hp
      exact prefix_trap_false hp (hall 0).1
    · obtain ⟨n, rfl⟩ : ∃ n, k = (b.wireLog wire dss.flatten).length + n :=
        ⟨k - (b.wireLog wire dss.flatten).length, by omega⟩
      have hm : (Shape.streamAppend (b.wireLog wire dss.flatten) (fun k => b.wireCall wire (y k))
          ((b.wireLog wire dss.flatten).length + n)) = b.wireCall wire (y n) := by
        rw [Shape.streamAppend_ge (by omega)]
        simp
      rw [hm] at hk
      have hz2 : (y n).2 = none := sumAns_eq_inr hk
      exact chain_trap_false hp (fun k => (hall k).1) n (impRel_trap (hall n).2 hz2)

/-- **No plain traps**: every trap of the importer keeps its store. -/
theorem noPlainTrap_impTripleS : StratSession.NoPlainTrap (b.impTripleS P wire I) := by
  intro u q c hx
  rcases hx with ⟨-, hx⟩ | ⟨j, vs, f, cs, dss, -, -, -, ⟨w, u₁, -, hx⟩ | ⟨s, t, -, -, hx⟩⟩ <;>
    simp at hx

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink
