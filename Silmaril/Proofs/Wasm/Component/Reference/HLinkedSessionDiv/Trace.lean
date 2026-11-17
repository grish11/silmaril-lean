module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Main
public import Silmaril.Proofs.Wasm.Component.Reference.HostWrite.Runs

/-!
# Diverging calls of `HLinked2.toRef`, backward: explicit infinite runs

The backward classification of a quietly diverging call follows one infinite run of the machine,
given explicitly as a sequence of configurations, so that the configurations it meets can be
compared by their positions:

* `IRun t`: `t` is an infinite run of internal steps; `IRun.lrun`: a live deterministic run
  from `t p` is followed by `t` (`t (p + tr.length)` is its end); `IRun.steps`: the segment
  between two positions is a finite run without host events; `IRun.diverges`;
* `IRun.core`: from a core activation at `t p`, the run stays in the core phase forever (an
  infinite core run, every configuration in the frame's host state) or leaves it at a position
  `n ≥ p` through a `CoreExit`;
* `callQuiet_irun`: a quietly diverging call is the invocation followed by an infinite internal
  run on which the host state `st` occurs at unboundedly late positions.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- An explicit infinite run of internal steps. -/
def IRun (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → Canon.P E σ (Ret E))
    (t : ℕ → Machine.Config E σ) : Prop :=
  ∀ n, InternalStep prof hr dispatch (t n) (t (n + 1))

theorem IRun.shift {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t) (k : ℕ) :
    IRun prof hr dispatch (fun n => t (k + n)) := fun n => by
  simpa [Nat.add_assoc] using h (k + n)

theorem IRun.diverges {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t) (n : ℕ) :
    Diverges prof hr dispatch (t n) :=
  ⟨fun k => t (n + k), by simp, fun k => by simpa [Nat.add_assoc] using h (n + k)⟩

/-- **A live deterministic run is followed by every infinite run.** -/
theorem IRun.lrun {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t)
    {m m' : Machine.Config E σ} {tr : List (Label E σ)} (hl : LRun prof hr dispatch m tr m') :
    ∀ {p : ℕ}, t p = m → t (p + tr.length) = m' := by
  induction hl with
  | refl => intro p hp; simpa using hp
  | @cons m m₁ m₂ l tr _ hu _ ih =>
    intro p hp
    obtain ⟨l', -, s⟩ := h p
    rw [hp] at s
    obtain ⟨-, e⟩ := hu.2 _ _ s
    have := ih (p := p + 1) e
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- The segment of an infinite run between two positions is a finite run without host events. -/
theorem IRun.steps {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t) (a : ℕ) :
    ∀ d, ∃ tr, Steps prof hr dispatch (t a) tr (t (a + d)) ∧ ∀ ev, Label.host ev ∉ tr
  | 0 => ⟨[], .refl _, fun _ h => nomatch h⟩
  | d + 1 => by
    obtain ⟨tr, r, hq⟩ := IRun.steps h a d
    obtain ⟨l, hl, s⟩ := h (a + d)
    refine ⟨tr ++ [l], Adequacy.steps_append r (.cons s (.refl _)), fun ev hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact hq ev hm
    · simp only [List.mem_singleton] at hm
      exact hl ev hm.symm

theorem IRun.steps_le {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t) {a b : ℕ}
    (hab : a ≤ b) : ∃ tr, Steps prof hr dispatch (t a) tr (t b) ∧ ∀ ev, Label.host ev ∉ tr := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact IRun.steps h a d

/-- **A core activation on an infinite run** stays in the core phase forever, or leaves it. -/
theorem IRun.core {t : ℕ → Machine.Config E σ} (h : IRun prof hr dispatch t)
    {B : Machine.Config E σ} {th : Option ThreadId} {K : List FlatValue → Canon.P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)} {x : CoreSt E} {p : ℕ}
    (hp : t p = coreCfg B th K segs rest x) :
    (Silmaril.InfiniteTrace (CoreStep E) x ∧ ∀ n, p ≤ n → (t n).host = B.host) ∨
      ∃ n, p ≤ n ∧ ∃ (y : CoreSt E) (lb : Label E σ), t n = coreCfg B th K segs rest y ∧
        Relation.ReflTransGen (CoreStep E) x y ∧ CoreExit B th K segs rest y lb (t (n + 1)) ∧
        (∀ ev, lb ≠ .host ev) ∧ Step prof hr dispatch (t n) lb (t (n + 1)) := by
  classical
  by_cases hex : ∃ n, p ≤ n ∧ ∃ (y : CoreSt E) (lb : Label E σ), t n = coreCfg B th K segs rest y ∧
      Relation.ReflTransGen (CoreStep E) x y ∧ CoreExit B th K segs rest y lb (t (n + 1)) ∧
      (∀ ev, lb ≠ .host ev) ∧ Step prof hr dispatch (t n) lb (t (n + 1))
  · exact .inr hex
  have hall : ∀ d, ∃ y, t (p + d) = coreCfg B th K segs rest y ∧
      Relation.ReflTransGen (CoreStep E) x y := by
    intro d
    induction d with
    | zero => exact ⟨x, by simpa using hp, .refl⟩
    | succ d ih =>
      obtain ⟨y, hy, hxy⟩ := ih
      obtain ⟨lb, hlb, s⟩ := h (p + d)
      rw [hy] at s
      rcases coreCfg_step_inv s with ⟨-, y', hy', e⟩ | hx
      · exact ⟨y', by rw [← Nat.add_assoc, e], hxy.tail hy'⟩
      · exact (hex ⟨p + d, Nat.le_add_right _ _, y, lb, hy, hxy, hx, hlb, hy ▸ s⟩).elim
  refine .inl ⟨?_, fun n hn => ?_⟩
  · refine Silmaril.InfiniteTrace.coinduct (fun y => ∃ d, t (p + d) = coreCfg B th K segs rest y ∧
      Relation.ReflTransGen (CoreStep E) x y) (fun y ⟨d, hy, hxy⟩ => ?_) ⟨0, by simpa using hp, .refl⟩
    obtain ⟨lb, hlb, s⟩ := h (p + d)
    rw [hy] at s
    rcases coreCfg_step_inv s with ⟨-, y', hy', e⟩ | hx
    · exact ⟨y', hy', d + 1, by rw [← Nat.add_assoc, e], hxy.tail hy'⟩
    · exact (hex ⟨p + d, Nat.le_add_right _ _, y, lb, hy, hxy, hx, hlb, hy ▸ s⟩).elim
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨y, hy, -⟩ := hall d
    rw [hy]
    rfl

/-! ## Quiet divergence as an explicit run -/

section Quiet

variable {st : σ}

/-- One step of an explicit run, counting down to the next configuration in host state `st`. -/
def CStep (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → Canon.P E σ (Ret E))
    (st : σ) (a b : Machine.Config E σ × ℕ) : Prop :=
  InternalStep prof hr dispatch a.1 b.1 ∧ (a.2 = b.2 + 1 ∨ (a.2 = 0 ∧ a.1.host = st))

theorem cstep_hits {T : ℕ → Machine.Config E σ × ℕ}
    (hT : ∀ n, CStep prof hr dispatch st (T n) (T (n + 1))) :
    ∀ d N, (T N).2 = d → ∃ n, N ≤ n ∧ (T n).1.host = st := by
  intro d
  induction d with
  | zero =>
    intro N hN
    rcases (hT N).2 with h | ⟨-, h⟩
    · omega
    · exact ⟨N, le_rfl, h⟩
  | succ d ih =>
    intro N hN
    rcases (hT N).2 with h | ⟨h, -⟩
    · obtain ⟨n, hn, hs⟩ := ih (N + 1) (by omega)
      exact ⟨n, by omega, hs⟩
    · omega

/-- **A quiet divergence in host state `st` is an explicit infinite internal run** on which `st`
occurs at unboundedly late positions. -/
theorem quiet_irun {m : Machine.Config E σ} {tr : List (Label E σ)} {q : Machine.Config E σ}
    (hs : Steps prof hr dispatch m tr q) (hh : ∀ ev, Label.host ev ∉ tr)
    (hq : QuietDiverges prof hr dispatch st q) :
    ∃ t : ℕ → Machine.Config E σ, t 0 = m ∧ IRun prof hr dispatch t ∧
      ∀ N, ∃ n, N ≤ n ∧ (t n).host = st := by
  let Q : Machine.Config E σ × ℕ → Prop := fun a => ∃ tr q, Steps prof hr dispatch a.1 tr q ∧
    tr.length = a.2 ∧ (∀ ev, Label.host ev ∉ tr) ∧ QuietDiverges prof hr dispatch st q
  have hstep : ∀ a, Q a → ∃ b, CStep prof hr dispatch st a b ∧ Q b := by
    rintro ⟨a, d⟩ ⟨tr, q, r, hlen, hh, hqd⟩
    cases r with
    | refl =>
      obtain ⟨q', ⟨hqs, -, tr', r', hne, hh'⟩, hqd'⟩ := hqd.unfold
      cases r' with
      | refl => exact absurd rfl hne
      | @cons _ b _ l tr'' s r'' =>
        refine ⟨(b, tr''.length), ⟨⟨l, fun ev e => hh' ev (e ▸ List.mem_cons_self), s⟩,
          .inr ⟨by simpa using hlen.symm, hqs⟩⟩, tr'', q', r'', rfl,
          fun ev hm => hh' ev (List.mem_cons_of_mem _ hm), hqd'⟩
    | @cons _ b _ l tr' s r' =>
      refine ⟨(b, tr'.length), ⟨⟨l, fun ev e => hh ev (e ▸ List.mem_cons_self), s⟩,
        .inl (by simpa using hlen.symm)⟩, tr', q, r', rfl,
        fun ev hm => hh ev (List.mem_cons_of_mem _ hm), hqd⟩
  obtain ⟨T, hT0, hT⟩ := Silmaril.InfiniteTrace.coinduct (R := CStep prof hr dispatch st) Q hstep
    (a := (m, tr.length)) ⟨tr, q, hs, rfl, hh, hq⟩
  refine ⟨fun n => (T n).1, by simp [hT0], fun n => (hT n).1, fun N => ?_⟩
  exact cstep_hits hT _ N rfl

/-- **A quietly diverging call**: the invocation, then an explicit infinite internal run on which
the host state `st` occurs at unboundedly late positions. -/
theorem callQuiet_irun {m : Machine.Config E σ} {c : CallId} {f : FuncId}
    {args : List Silmaril.Wasm.Component.Reference.Val}
    (h : CallQuietDiverges prof hr dispatch m c f args st) :
    ∃ (m₁ : Machine.Config E σ) (t : ℕ → Machine.Config E σ),
      Step prof hr dispatch m (.host (invokeTop c f args)) m₁ ∧ t 0 = m₁ ∧
        IRun prof hr dispatch t ∧ ∀ N, ∃ n, N ≤ n ∧ (t n).host = st := by
  obtain ⟨m₁, tr, m₂, s, r, hh, hq⟩ := h
  obtain ⟨t, ht0, ht, hio⟩ := quiet_irun r hh hq
  exact ⟨m₁, t, s, ht0, ht, hio⟩

end Quiet

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
