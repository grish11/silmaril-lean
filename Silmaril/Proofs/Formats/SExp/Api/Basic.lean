module

public import Silmaril.Formats.SExp.Api.Defs
public import Silmaril.Formats.SExp.Family.Thms

/-! # Proofs: S-expression APIs as AST APIs, child relations, monotone readers, certificates -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Api

open Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle

variable {α : Type} {H : Type}

theorem toAST_ofList (cs : List (SExp α)) :
    SExp.toAST (SExp.ofList cs) = TExpr.ofList ⟨SxTag.branch, ()⟩ (cs.map SExp.toAST) := by
  apply (TExpr.equivNode _ _).injective
  simp [TExpr.equivNode, TExpr.node, TExpr.ofList, SExp.toAST, SExp.ofList]

theorem sexpW_hom : (sexpW α).Hom (astW (sexpSig α)) SxOp.toAST SExp.toAST := by
  refine ⟨SExp.toAST_injective, ?_⟩
  intro op ts
  cases op with
  | atom a =>
      cases ts with
      | nil =>
          simp only [astW, SxOp.toAST, sexpW, List.map_nil, List.length_nil, Option.map_some]
          simp only [sexpSig, Arity.Admits, beq_self_eq_true, ite_true]
          simp only [TExpr.ofList, SExp.toAST, List.length_nil]
          exact congrArg some (congrArg (TExpr.tag _ 0) (funext fun i => i.elim0))
      | cons c cs =>
          simp only [astW, sexpW, SxOp.toAST]
          split
          · rename_i h
            simp [sexpSig, Arity.Admits] at h
            exact absurd h (List.cons_ne_nil _ _)
          · rfl
  | list =>
      simp only [astW, SxOp.toAST, sexpW, sexpSig, Arity.Admits, ite_true]
      exact congrArg some (toAST_ofList ts).symm

theorem sexpW_childRel : (sexpW α).ChildRel SExp.Child := by
  intro op ts t hb c hc
  obtain ⟨cs, rfl, hcs⟩ := hc
  cases op with
  | atom a =>
      cases ts with
      | nil =>
          simp only [sexpW, Option.some.injEq] at hb
          cases cs <;> simp [SExp.ofList] at hb
      | cons _ _ => simp [sexpW] at hb
  | list =>
      simp only [sexpW, Option.some.injEq] at hb
      rw [SExp.ofList_injective hb]
      exact hcs

theorem consW_childRel : (consW α).ChildRel SExp2.Child := by
  intro op ts t hb c hc
  obtain ⟨x, y, rfl, hxy⟩ := hc
  rcases op with _ | a | _ <;> rcases ts with _ | ⟨p, _ | ⟨q, _ | ⟨r, ts⟩⟩⟩ <;>
    simp [consW] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rcases hxy with rfl | rfl <;> simp

theorem sexpR_mono : (sexpR α H).Mono := by
  constructor
  · intro ρ ρ' q hext hv
    cases q with
    | kind h => obtain ⟨x, hx⟩ := hv; exact ⟨x, hext hx⟩
    | atom h => obtain ⟨a, ha⟩ := hv; exact ⟨a, hext ha⟩
    | items h => obtain ⟨cs, hc⟩ := hv; exact ⟨cs, hext hc⟩
    | count h => obtain ⟨cs, hc⟩ := hv; exact ⟨cs, hext hc⟩
    | child h i => obtain ⟨cs, hc, hi⟩ := hv; exact ⟨cs, hext hc, hi⟩
  · intro ρ ρ' q a hext _ hok
    cases q <;> cases a <;> simp only [sexpR] at hok ⊢
    · obtain ⟨x, hx, rfl⟩ := hok; exact ⟨x, hext hx, rfl⟩
    · exact hext hok
    · obtain ⟨cs, hc, hF⟩ := hok
      exact ⟨cs, hext hc, hF.imp fun _ _ h => hext h⟩
    · obtain ⟨cs, hc, hn⟩ := hok; exact ⟨cs, hext hc, hn⟩
    · obtain ⟨cs, c, hc, hi, hh⟩ := hok; exact ⟨cs, c, hext hc, hi, hext hh⟩

theorem consR_mono : (consR α H).Mono := by
  constructor
  · intro ρ ρ' q hext hv
    cases q with
    | kind h => obtain ⟨x, hx⟩ := hv; exact ⟨x, hext hx⟩
    | atom h => obtain ⟨a, ha⟩ := hv; exact ⟨a, hext ha⟩
    | car h => obtain ⟨x, y, hx⟩ := hv; exact ⟨x, y, hext hx⟩
    | cdr h => obtain ⟨x, y, hx⟩ := hv; exact ⟨x, y, hext hx⟩
  · intro ρ ρ' q a hext _ hok
    cases q <;> cases a <;> simp only [consR] at hok ⊢
    · obtain ⟨x, hx, rfl⟩ := hok; exact ⟨x, hext hx, rfl⟩
    · exact hext hok
    · obtain ⟨x, y, hx, hh⟩ := hok; exact ⟨x, y, hext hx, hext hh⟩
    · obtain ⟨x, y, hx, hh⟩ := hok; exact ⟨x, y, hext hx, hext hh⟩

theorem astR_mono {S : AstSig} : (astR S H).Mono := by
  constructor
  · intro ρ ρ' q hext hv
    cases q with
    | tag h => obtain ⟨x, hx⟩ := hv; exact ⟨x, hext hx⟩
    | count h => obtain ⟨x, hx⟩ := hv; exact ⟨x, hext hx⟩
    | child h i => obtain ⟨v, cs, hx, hi⟩ := hv; exact ⟨v, cs, hext hx, hi⟩
  · intro ρ ρ' q a hext _ hok
    cases q <;> cases a <;> simp only [astR] at hok ⊢
    · obtain ⟨cs, hx⟩ := hok; exact ⟨cs, hext hx⟩
    · obtain ⟨v, cs, hx, hn⟩ := hok; exact ⟨v, cs, hext hx, hn⟩
    · obtain ⟨v, cs, c, hx, hi, hh⟩ := hok; exact ⟨v, cs, c, hext hx, hi, hext hh⟩

theorem consChain_sound {ρ : Env H (SExp2 α)} {hist : List (ConsQ H × ConsA α H)}
    (hf : ∀ p ∈ hist, (consR α H).valid ρ p.1 ∧ (consR α H).ok ρ p.1 p.2) :
    ∀ {h : H} {as : List α}, ConsChain hist h as → ρ h = some (SExp2.ofAtoms as) := by
  intro h as hc
  induction hc with
  | nil hk =>
      obtain ⟨x, hx, hk⟩ := (hf _ hk).2
      cases x <;> simp [consKind] at hk
      simpa [SExp2.ofAtoms, SExp2.ofList] using hx
  | cons hk hcar hcdr hat _ ih =>
      obtain ⟨x, y, hx, hh⟩ := (hf _ hcar).2
      obtain ⟨x', y', hx', hh'⟩ := (hf _ hcdr).2
      have ha := (hf _ hat).2
      simp only [consR] at ha
      rw [hx] at hx'
      simp only [Option.some.injEq, SExp2.cons.injEq] at hx'
      obtain ⟨rfl, rfl⟩ := hx'
      rw [ha] at hh
      rw [ih] at hh'
      simp only [Option.some.injEq] at hh hh'
      subst hh hh'
      simpa [SExp2.ofAtoms, SExp2.ofList] using hx

theorem listCert_sound (P : List α → Prop) :
    CertSound (consR α H) (listCert P) {x | ∃ as, x = SExp2.ofAtoms as ∧ P as} := by
  intro ρ hist h hf ⟨as, hc, hP⟩ t ht
  rw [consChain_sound hf hc] at ht
  exact ⟨as, (Option.some.inj ht).symm, hP⟩

end Silmaril.Proofs.Formats.SExp.Api
