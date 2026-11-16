module

public import Silmaril.Wasm.Abstract.BodyStrat.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# Bodies into the canonical play object: proofs

Saturation of a body's triple: every call prefix forced by a finished path,
a pending call or an infinite run of the tree is a pending call of the tree.
-/

public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.BodyStrat

universe u

variable {E : Sig.{u}} {Y : Type (u + 1)}

/-- A pending call after `c ++ ⟨m, n⟩ :: c'` makes `m` pending after `c`. -/
theorem pend_prefix {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {c c' : List (Call E)}
    {m m' : E.Op} {n : E.Ar m} (h : Pend t (c ++ ⟨m, n⟩ :: c') m') : Pend t c m := by
  generalize hl : c ++ ⟨m, n⟩ :: c' = l at h
  induction h generalizing c with
  | here _ => cases c <;> simp at hl
  | @vis t R e k n₀ cs m'' ht _ ih =>
    cases c with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      have hm : m = e.1 := congrArg Sigma.fst hl.1
      subst hm
      exact .here ht
    | cons x c =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      exact .vis ht (ih hl)

/-- A finished path through `c ++ ⟨m, n⟩ :: c'` makes `m` pending after `c`. -/
theorem path_prefix {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {c c' : List (Call E)}
    {m : E.Op} {n : E.Ar m} {r : PathEnd Y} (h : Path t (c ++ ⟨m, n⟩ :: c') r) : Pend t c m := by
  generalize hl : c ++ ⟨m, n⟩ :: c' = l at h
  induction h generalizing c with
  | ret _ => cases c <;> simp at hl
  | div _ => cases c <;> simp at hl
  | @vis t R e k n₀ cs r ht _ ih =>
    cases c with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      have hm : m = e.1 := congrArg Sigma.fst hl.1
      subst hm
      exact .here ht
    | cons x c =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      exact .vis ht (ih hl)

/-- `streamTake` is `Stream'.take`. -/
theorem streamTake_eq_take {α : Type u} (ω : Stream' α) (k : ℕ) :
    streamTake ω k = Stream'.take k ω := by
  apply List.ext_getElem (by simp only [streamTake, List.length_ofFn]; exact (Stream'.length_take k ω).symm)
  intro i h₁ h₂
  have h := Stream'.getElem?_take (s := ω) (by simpa [streamTake] using h₁)
  rw [List.getElem?_eq_getElem h₂] at h
  simp only [streamTake, List.getElem_ofFn]
  exact (Option.some.inj h).symm

/-- An infinite run makes each of its calls pending after the calls before it. -/
theorem infPath_pend {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {ω : Stream' (Call E)}
    (h : InfPath t ω) (k : ℕ) : Pend t (streamTake ω k) (ω k).1 := by
  obtain ⟨m, hm⟩ := infPath_iff_pend.1 h (k + 1)
  rw [Stream'.take_succ', ← streamTake_eq_take] at hm
  exact pend_prefix (n := (ω k).2) hm

/-- Splitting a lifted call list. -/
theorem map_liftCall_eq {cs : List (Call E)} {c c' : List (Call (liftSig E))}
    {m : (liftSig E).Op} {n : (liftSig E).Ar m} (h : cs.map liftCall = c ++ ⟨m, n⟩ :: c') :
    ∃ c₀ m₀ n₀ c₀', cs = c₀ ++ (⟨m₀, n₀⟩ : Call E) :: c₀' ∧ c = c₀.map liftCall ∧
      m = ULift.up m₀ := by
  obtain ⟨l₁, l₂, rfl, rfl, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨⟨m₀, n₀⟩, l₃, rfl, hx, -⟩ := List.map_eq_cons_iff.1 h₂
  exact ⟨l₁, m₀, n₀, l₃, rfl, rfl, (congrArg Sigma.fst hx).symm⟩

variable {S T A B : Type (u + 1)}

/-- **The triple of a body is saturated.** -/
theorem toTriple_saturated (f : Hom E S T A B) : StratObs.Saturated (toTriple f) := by
  refine StratObs.saturated_iff.2 ?_
  funext s a
  ext ⟨c, m⟩
  refine ⟨?_, fun h => .inl h⟩
  rintro (h | ⟨d, m', ⟨cs, m'', hp, hd'⟩, n, c', hd⟩ | ⟨d, e, ⟨cs, r, hp, he⟩, n, c', hd⟩ |
    ⟨ω, ⟨ω', hω, rfl⟩, k, hk, hm⟩)
  · exact h
  · obtain ⟨rfl, -⟩ := Prod.mk.inj hd'
    obtain ⟨c₀, m₀, n₀, c₀', rfl, rfl, rfl⟩ := map_liftCall_eq hd
    exact ⟨c₀, m₀, pend_prefix (n := n₀) hp, rfl⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj he
    obtain ⟨c₀, m₀, n₀, c₀', rfl, rfl, rfl⟩ := map_liftCall_eq hd
    exact ⟨c₀, m₀, path_prefix (n := n₀) hp, rfl⟩
  · subst hk hm
    refine ⟨streamTake ω' k, (ω' k).1, infPath_pend hω k, ?_⟩
    simp [streamTake, List.map_ofFn, liftCall]
    rfl

end Silmaril.Proofs.Wasm.Abstract.BodyStrat
