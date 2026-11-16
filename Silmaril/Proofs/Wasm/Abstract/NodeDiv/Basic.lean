module

public import Silmaril.Wasm.Abstract.NodeDiv.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.Component.DWiringLaws.Thms

/-!
# Divergence of a Core 3.0 core node (proofs)

* `inv_of_path`: an instance path from an idle store is completed session rounds of
  `instTripleS`, then the current round (the converse is `path_of_rounds`);
* `mem_div_spullD_instSession`: the divergences of the read-back instance session are the
  instance paths to a running state that diverges host-free (`StratSession.mem_div_iff`);
* `not_silentChatter_of_allCall`: a handler that always calls has no silent chatter;
* `div_semOfSD`: no chatter at `importH` (it always calls) nor at `exportH` (one call).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeDiv

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.StratSession (threadS sroundsMoves sroundMoves)
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.NodeDiv (stream prependStream)
open Silmaril.Wasm.Abstract.InstStrat (Diverges instInf)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Moves -/

theorem callMoves_snoc {E F : Sig.{0}} (c : List (Call E)) (m : E.Op) (n : E.Ar m) :
    (callMoves (c ++ [⟨m, n⟩]) : List (Move E F)) =
      callMoves c ++ [.inl (.ask m), .inl (.ans m n)] := by
  simp [callMoves, List.flatMap_append]

theorem map_srelabel_callMoves {E : Sig.{0}} {ts : List FnType} (c : List (Call E)) :
    (callMoves (F := ifaceSig ts) c).map srelabel = callMoves (F := ssig ts) c := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [callMoves, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    rfl

/-! ## Instance paths -/

variable {I : ScalarInstance} {P : Profile}

theorem path_append {x y z : I.HState} {p q : List (Move I.E I.F)} (h₁ : I.Path P x p y)
    (h₂ : I.Path P y q z) : I.Path P x (p ++ q) z := by
  induction h₁ with
  | nil => exact h₂
  | cons ht _ ih => exact .cons ht (ih h₂)

theorem path_snoc {x z : I.HState} {p : List (Move I.E I.F)} {o : Move I.E I.F}
    (h : I.Path P x (p ++ [o]) z) : ∃ y, I.Path P x p y ∧ I.Trans P y o z := by
  induction p generalizing x with
  | nil =>
    rw [List.nil_append] at h
    cases h with
    | cons ht hp => cases hp; exact ⟨x, .nil _, ht⟩
  | cons m p ih =>
    rw [List.cons_append] at h
    cases h with
    | cons ht hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons ht h₁, h₂⟩

theorem path_single {x y : I.HState} {o : Move I.E I.F} (h : I.Trans P x o y) :
    I.Path P x [o] y :=
  .cons h (.nil _)

theorem path_split {x z : I.HState} {p q : List (Move I.E I.F)} (h : I.Path P x (p ++ q) z) :
    ∃ y, I.Path P x p y ∧ I.Path P y q z := by
  induction p generalizing x with
  | nil => exact ⟨x, .nil _, h⟩
  | cons m p ih =>
    rw [List.cons_append] at h
    cases h with
    | cons ht hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons ht h₁, h₂⟩

/-! ## The instance triple -/

theorem mem_instFinS_ret {s s' : Store Nat} {a : I.F.Op} {c : List (Call I.E)}
    {b : Res I.exports ⊕ PUnit} :
    (c, End.ret b s') ∈ (instTripleS I P).1 s a ↔ ∃ v, b = sAns a v ∧
      I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a v)])) (.idle s') := by
  constructor
  · rintro (⟨v, s'', he, hp⟩ | ⟨he, -⟩)
    · cases he
      exact ⟨v, rfl, hp⟩
    · cases he
  · rintro ⟨v, rfl, hp⟩
    exact .inl ⟨v, s', rfl, hp⟩

theorem mem_instFinS_div {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (c, End.div) ∈ (instTripleS I P).1 s a ↔ ∃ s' t,
      I.Path P (.idle s) (.inr (.ask a) :: callMoves c) (.running a s' t) ∧
        Diverges P (s', t) := by
  constructor
  · rintro (⟨v, s'', he, -⟩ | ⟨-, h⟩)
    · cases he
    · exact h
  · intro h
    exact .inr ⟨rfl, h⟩

theorem rounds_snoc {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s s₁ s₂ : S}
    {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} {b : B}
    (h : Rounds t s rs s₁) (hb : (c, .ret b s₂) ∈ t.1 s₁ a) :
    Rounds t s (rs ++ [(a, c, b)]) s₂ := by
  induction h with
  | nil => exact .cons hb (.nil _)
  | cons h₁ _ ih => exact .cons h₁ (ih hb)

/-- Completed session rounds of the instance triple are instance paths between idle states. -/
theorem path_of_rounds {s s' : Store Nat}
    {rs : List (I.F.Op × List (Call I.E) × (Res I.exports ⊕ PUnit))}
    (h : Rounds (instTripleS I P) s rs s') :
    ∃ p, I.Path P (.idle s) p (.idle s') ∧ p.map srelabel = sroundsMoves rs := by
  induction h with
  | nil => exact ⟨[], .nil _, rfl⟩
  | @cons s s₁ s₂ a c b rs hb _ ih =>
    obtain ⟨v, rfl, hp⟩ := mem_instFinS_ret.1 hb
    obtain ⟨p, hp', he⟩ := ih
    refine ⟨_, path_append hp hp', ?_⟩
    simp only [sroundsMoves, List.flatMap_cons] at he ⊢
    rw [List.map_append, he]
    simp only [sroundMoves, List.map_cons, List.map_append, map_srelabel_callMoves,
      List.map_nil]
    rfl

/-- The invariant of an instance path from the idle store `s`: completed session rounds, then
the current round. -/
def Inv (I : ScalarInstance) (P : Profile) (s : Store Nat) (p : List (Move I.E I.F)) :
    I.HState → Prop
  | .idle s' => ∃ rs, Rounds (instTripleS I P) s rs s' ∧ p.map srelabel = sroundsMoves rs
  | .running f u t => ∃ rs s₁ c, Rounds (instTripleS I P) s rs s₁ ∧
      I.Path P (.idle s₁) (.inr (.ask f) :: callMoves c) (.running f u t) ∧
      p.map srelabel =
        sroundsMoves rs ++ (.inr (.ask f) :: callMoves c : List (Move I.E (ssig I.exports)))
  | .waiting f u t e => ∃ rs s₁ c, Rounds (instTripleS I P) s rs s₁ ∧
      I.Path P (.idle s₁) (.inr (.ask f) :: (callMoves c ++ [.inl (.ask e)])) (.waiting f u t e) ∧
      p.map srelabel = sroundsMoves rs ++
        (.inr (.ask f) :: (callMoves c ++ [.inl (.ask e)]) : List (Move I.E (ssig I.exports)))

theorem inv_of_path {s : Store Nat} {p : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.idle s) p q) : Inv I P s p q := by
  induction p using List.reverseRecOn generalizing q with
  | nil => cases h; exact ⟨[], .nil _, rfl⟩
  | append_singleton p o ih =>
    obtain ⟨y, hy, ht⟩ := path_snoc h
    have hi := ih hy
    cases ht with
    | call s₁ f =>
      obtain ⟨rs, hrs, he⟩ := hi
      refine ⟨rs, s₁, [], hrs, path_single (.call s₁ f), ?_⟩
      rw [List.map_append, he]
      rfl
    | ucall run callout op =>
      obtain ⟨rs, s₁, c, hrs, hp, he⟩ := hi
      refine ⟨rs, s₁, c, hrs, ?_, ?_⟩
      · have := path_append hp (path_single (.ucall run callout op))
        simpa using this
      · rw [List.map_append, he]
        simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append]
        rfl
    | uret v =>
      obtain ⟨rs, s₁, c, hrs, hp, he⟩ := hi
      refine ⟨rs, s₁, c ++ [⟨_, v⟩], hrs, ?_, ?_⟩
      · have := path_append hp (path_single (.uret v))
        rw [callMoves_snoc]
        simpa using this
      · rw [List.map_append, he, callMoves_snoc]
        simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
          List.nil_append]
        rfl
    | @oret f _ s' _ _ _ v run final answer =>
      obtain ⟨rs, s₁, c, hrs, hp, he⟩ := hi
      refine ⟨rs ++ [(f, c, sAns f v)], rounds_snoc hrs (mem_instFinS_ret.2 ⟨v, rfl, ?_⟩), ?_⟩
      · have := path_append hp (path_single (.oret run final answer))
        simpa using this
      · rw [List.map_append, he]
        simp only [sroundsMoves, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, sroundMoves, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append]
        rfl

/-- **The divergences of the read-back instance session** are the instance paths from `s` to a
running state that diverges host-free. -/
theorem mem_div_spullD_instSession {s : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ (spullD (instSession I P s)).div ↔
      ∃ a u t, I.Path P (.idle s) p (.running a u t) ∧ Diverges P (u, t) := by
  rw [mem_div_spullD]
  constructor
  · intro h
    obtain ⟨rs, s₁, a, c, hrs, hd, he⟩ := StratSession.mem_div_iff.1 h
    obtain ⟨u, t, hp, hdv⟩ := mem_instFinS_div.1 hd
    obtain ⟨p₀, hp₀, he₀⟩ := path_of_rounds hrs
    have hpe : p = p₀ ++ .inr (.ask a) :: callMoves c := by
      apply (List.map_injective_iff.2 (srelabel_injective (E := I.E) (ts := I.exports)))
      rw [he, List.map_append, he₀, List.map_cons, map_srelabel_callMoves]
      rfl
    exact ⟨a, u, t, hpe ▸ path_append hp₀ hp, hdv⟩
  · rintro ⟨a, u, t, hp, hdv⟩
    obtain ⟨rs, s₁, c, hrs, hp₁, he⟩ := inv_of_path hp
    rw [he]
    exact StratSession.mem_div.2 ⟨s₁, hrs, mem_instFinS_div.2 ⟨u, t, hp₁, hdv⟩⟩

/-! ## No chatter at the coercions -/

theorem not_silentChatter_of_allCall {E F G : Sig.{0}} {h : Handler E F} (hh : AllCall h)
    {σ : DStrategy F G} {s : List (Move E G)} : ¬ SilentChatter h σ s := by
  rintro ⟨J, hJ, t₀, ht₀, -, hsil, -⟩
  have hinf := σ.inf_isInf hJ
  obtain ⟨t₁, ht₁, hlen⟩ := hinf.unbounded (t₀.length + 1)
  rcases hinf.total ht₀ ht₁ with ⟨w, rfl⟩ | hpre
  · cases w with
    | nil => simp at hlen
    | cons x w' =>
      have hmem : t₀ ++ [] ++ [x] ∈ J := hinf.of_prefix ht₁ ⟨w', by simp⟩
      obtain ⟨e, rfl, he⟩ := hsil [] x hmem
      cases e with
      | ask q =>
        obtain ⟨r, hr⟩ := he
        obtain ⟨m, k, hk, -⟩ := hh q
        rw [hk] at hr
        cases hr
      | ans q r =>
        obtain ⟨m, k, hk, -⟩ := hh q
        have he' : h q = .pure r := he
        rw [hk] at he'
        cases he'
  · have := hpre.length_le
    omega

theorem allCall_importH (m : NumInstance) : AllCall (importH m) :=
  fun _ => ⟨_, _, rfl, fun _ => ⟨_, rfl⟩⟩

theorem oneCall_exportH (m : NumInstance) : OneCall (exportH m) := by
  intro q
  unfold exportH
  dsimp only
  split
  · split
    · exact Or.inr ⟨_, _, rfl, fun _ => ⟨_, rfl⟩⟩
    · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem div_semOfSD (m : NumInstance) (σ : DStrategy m.inst.E (ssig m.inst.exports)) :
    (semOfSD m σ).div = {p | ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧
      ∃ a b, Zip a b v ∧ a ∈ (spullD σ).div ∧ b ∈ Strategy.ofHandler (exportH m)} := by
  rw [semOfSD, DStrategy.div_ofHandler_comp_iff]
  ext p
  rw [Set.mem_ofPred_eq, or_iff_left (not_silentChatter_of_allCall (allCall_importH m)),
    DStrategy.div_comp_ofHandler (oneCall_exportH m)]
  rfl

theorem div_core3SemD_sem (P : Profile) (m : NumInstance) :
    ((core3SemD P).sem m).div = {p | ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧
      ∃ a b, Zip a b v ∧
        (∃ f s t, m.inst.Path P (.idle m.inst.store) a (.running f s t) ∧ Diverges P (s, t)) ∧
        b ∈ Strategy.ofHandler (exportH m)} := by
  show (semOfSD m (instSession m.inst P m.inst.store)).div = _
  rw [div_semOfSD]
  ext p
  simp only [Set.mem_ofPred_eq, mem_div_spullD_instSession]

/-! ## The productive stream of the current round -/

theorem length_callMoves {E F : Sig.{0}} (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [callMoves, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp
    omega

theorem streamTake_succ {α : Type} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  apply List.ext_getElem (by simp [streamTake])
  intro i h₁ h₂
  simp only [streamTake, List.getElem_ofFn]
  rcases Nat.lt_succ_iff_lt_or_eq.1 (by simpa [streamTake] using h₁) with h | rfl
  · rw [List.getElem_append_left (by simpa using h), List.getElem_ofFn]
  · simp

@[simp] theorem length_streamTake {α : Type} (ω : ℕ → α) (k : ℕ) :
    (streamTake ω k).length = k := by
  simp [streamTake]

theorem stream_mono {E F : Sig.{0}} (p₀ : List (Move E F)) (a : F.Op) (ω : ℕ → Call E) :
    (stream p₀ a ω).Mono := by
  intro k
  refine ⟨[.inl (.ask (ω k).1), .inl (.ans (ω k).1 (ω k).2)], ?_⟩
  simp [stream, streamTake_succ, callMoves, List.flatMap_append]

theorem stream_unbounded {E F : Sig.{0}} (p₀ : List (Move E F)) (a : F.Op) (ω : ℕ → Call E) :
    (stream p₀ a ω).Unbounded := by
  intro k
  refine ⟨k, ?_⟩
  simp only [stream, List.length_append, List.length_cons, length_callMoves, length_streamTake]
  omega

theorem image_lim {α β : Type} (f : α → β) (c : Chain α) :
    List.map f '' c.lim = Chain.lim fun k => (c k).map f := by
  ext q
  constructor
  · rintro ⟨q₀, ⟨n, hn⟩, rfl⟩
    exact ⟨n, hn.map f⟩
  · rintro ⟨n, hn⟩
    refine ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hn).symm

theorem map_stream {p₀ : List (Move I.E I.F)}
    {rs : List (I.F.Op × List (Call I.E) × (Res I.exports ⊕ PUnit))}
    (he : p₀.map srelabel = sroundsMoves rs) (a : I.F.Op) (ω : ℕ → Call I.E) :
    (fun k => (stream p₀ a ω k).map srelabel) = fun k =>
      sroundsMoves rs ++ (.inr (.ask a) :: callMoves (streamTake ω k) :
        List (Move I.E (ssig I.exports))) := by
  funext k
  rw [stream, List.map_append, he, List.map_cons, map_srelabel_callMoves]
  rfl

/-- **The productive stream of the current round** of the read-back instance session: after the
instance play `p₀`, the question `a` and the import calls `ω` forever are an infinite play iff
`p₀` ends idle at a store from which `ω` is a productive stream of `a`. -/
theorem mem_inf_spullD_instSession_stream {s : Store Nat} {p₀ : List (Move I.E I.F)}
    {a : I.F.Op} {ω : ℕ → Call I.E} :
    (stream p₀ a ω).lim ∈ (spullD (instSession I P s)).inf ↔
      ∃ s₁, I.Path P (.idle s) p₀ (.idle s₁) ∧ ω ∈ instInf I P s₁ a := by
  constructor
  · intro hJ
    have hm : p₀ ++ [.inr (.ask a)] ∈ (spullD (instSession I P s)).toStrategy :=
      (spullD (instSession I P s)).inf_sub hJ ⟨0, by simp [stream, streamTake, callMoves]⟩
    rw [toStrategy_spullD_instSession, ScalarInstance.mem_strategy_iff] at hm
    obtain ⟨q, hq⟩ := hm
    obtain ⟨y, hy, ht⟩ := path_snoc hq
    cases ht with
    | call s₁ f =>
      obtain ⟨rs, hrs, he⟩ := inv_of_path hy
      have h₂ := hJ.2
      rw [image_lim, map_stream he] at h₂
      obtain ⟨s', hrs', hω⟩ := StratSession.mem_inf.1 h₂
      obtain ⟨p₀', hp₀', he'⟩ := path_of_rounds hrs'
      have hpe : p₀' = p₀ :=
        List.map_injective_iff.2 (srelabel_injective (E := I.E) (ts := I.exports))
          (he'.trans he.symm)
      exact ⟨s', hpe ▸ hp₀', hω⟩
  · rintro ⟨s₁, hp, hω⟩
    obtain ⟨rs, hrs, he⟩ := inv_of_path hp
    refine ⟨Chain.isInfPlay_lim (stream_mono _ _ _) (stream_unbounded _ _ _), ?_⟩
    rw [image_lim, map_stream he]
    exact StratSession.mem_inf.2 ⟨s₁, hrs, hω⟩

/-! ## Import calls in the middle of a round -/

theorem prependStream_nil {α : Type} (c : ℕ → α) : prependStream [] c = c := by
  funext k
  simp [prependStream]

theorem prependStream_cons_zero {α : Type} (x : α) (l : List α) (c : ℕ → α) :
    prependStream (x :: l) c 0 = x := by
  simp [prependStream]

theorem prependStream_cons_succ {α : Type} (x : α) (l : List α) (c : ℕ → α) (k : ℕ) :
    prependStream (x :: l) c (k + 1) = prependStream l c k := by
  simp only [prependStream, List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
  split <;> simp

/-- The two moves of one import call. -/
theorem path_call_iff {x z : I.HState} {e : Call I.E} :
    I.Path P x (callMoves [e]) z ↔
      ∃ w, I.Trans P x (.inl (.ask e.1)) w ∧ I.Trans P w (.inl (.ans e.1 e.2)) z := by
  constructor
  · intro h
    cases h with
    | cons h₁ h' =>
      cases h' with
      | cons h₂ h'' =>
        cases h''
        exact ⟨_, h₁, h₂⟩
  · rintro ⟨w, h₁, h₂⟩
    exact .cons h₁ (.cons h₂ (.nil _))

theorem calls_prepend {cs : List (Call I.E)} {c : ℕ → Call I.E} :
    ∀ {y z : I.HState}, I.Path P y (callMoves cs) z →
      (∃ q : ℕ → I.HState, q 0 = z ∧ ∀ k, I.Path P (q k) (callMoves [c k]) (q (k + 1))) →
      ∃ q : ℕ → I.HState, q 0 = y ∧
        ∀ k, I.Path P (q k) (callMoves [prependStream cs c k]) (q (k + 1)) := by
  induction cs with
  | nil =>
    intro y z h hq
    cases h
    rw [prependStream_nil]
    exact hq
  | cons x cs ih =>
    intro y z h hq
    have h' : I.Path P y (callMoves [x] ++ callMoves cs) z := by
      simpa [callMoves] using h
    obtain ⟨w, hw, hz⟩ := path_split h'
    obtain ⟨q, hq0, hq⟩ := ih hz hq
    refine ⟨fun k => match k with | 0 => y | k + 1 => q k, rfl, ?_⟩
    rintro (_ | k)
    · rw [prependStream_cons_zero]
      show I.Path P y _ (q 0)
      rw [hq0]
      exact hw
    · rw [prependStream_cons_succ]
      exact hq k

/-- **Import calls forever, in the middle of a round, are a productive stream of the round**:
the import calls `cs` so far, then `c`. -/
theorem instInf_of_calls {u s : Store Nat} {f : I.F.Op} {cs : List (Call I.E)}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {q : ℕ → I.HState} {c : ℕ → Call I.E}
    (hp : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t))
    (hq0 : q 0 = .running f s t) (hq : ∀ k, I.Path P (q k) (callMoves [c k]) (q (k + 1))) :
    prependStream cs c ∈ instInf I P u f := by
  cases hp with
  | cons h₁ hp' =>
    cases h₁
    obtain ⟨x, hx0, hx⟩ := calls_prepend hp' ⟨q, hq0, hq⟩
    exact ⟨x, hx0, fun k => path_call_iff.1 (hx k)⟩

theorem running_of_instInf {u : Store Nat} {f : I.F.Op} {ω : ℕ → Call I.E}
    {x : ℕ → I.HState} (hx0 : x 0 = .running f u (I.initThread f))
    (hx : ∀ k, ∃ y, I.Trans P (x k) (.inl (.ask (ω k).1)) y ∧
      I.Trans P y (.inl (.ans (ω k).1 (ω k).2)) (x (k + 1))) :
    ∀ n, ∃ s t, x n = .running f s t
  | 0 => ⟨_, _, hx0⟩
  | n + 1 => by
    obtain ⟨s, t, hn⟩ := running_of_instInf hx0 hx n
    obtain ⟨y, h₁, h₂⟩ := hx n
    rw [hn] at h₁
    cases h₁ with
    | ucall run callout op =>
      generalize x (n + 1) = z at h₂ ⊢
      cases h₂
      exact ⟨_, _, rfl⟩

/-- **A productive stream of a round, cut after `n` calls**: the round's path so far ends
running, and the remaining calls are made one by one from there. -/
theorem calls_of_instInf {u : Store Nat} {f : I.F.Op} {ω : ℕ → Call I.E}
    (hω : ω ∈ instInf I P u f) (n : ℕ) :
    ∃ s t, ∃ q : ℕ → I.HState,
      I.Path P (.idle u) (.inr (.ask f) :: callMoves (streamTake ω n)) (.running f s t) ∧
      q 0 = .running f s t ∧ ∀ k, I.Path P (q k) (callMoves [ω (n + k)]) (q (k + 1)) := by
  obtain ⟨x, hx0, hx⟩ := hω
  have hpath : ∀ n, I.Path P (.idle u) (.inr (.ask f) :: callMoves (streamTake ω n)) (x n) := by
    intro n
    induction n with
    | zero => rw [hx0]; exact path_single (.call u f)
    | succ n ih =>
      rw [streamTake_succ, callMoves_snoc]
      have := path_append ih (path_call_iff.2 (hx n))
      simpa [callMoves] using this
  obtain ⟨s, t, hn⟩ := running_of_instInf hx0 hx n
  refine ⟨s, t, fun k => x (n + k), hn ▸ hpath n, hn, fun k => ?_⟩
  rw [path_call_iff]
  exact hx (n + k)

end Silmaril.Proofs.Wasm.Abstract.NodeDiv
