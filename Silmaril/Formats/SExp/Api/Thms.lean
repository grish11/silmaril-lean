module

public import Silmaril.Formats.SExp.Api.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Formats.SExp.Api.Basic

/-!
# Handle APIs for S-expressions: laws

* `sexpW_hom`: the S-expression writer is a writer homomorphism into the AST writer of
  `sexpSig α` (operations by `SxOp.toAST`, trees by `SExp.toAST`). Hence
  `sexpLang_eq_astLang`: without undefined behaviour, a module using the generic AST API with the
  S-expression signature accepts exactly the `toAST` image of what the same module accepts
  through the first-class S-expression API, for every atom family at once.
* child relations: `sexpW_childRel`, `consW_childRel`, so the constructed-set languages are
  downward closed (`sexpLang_all_downClosed`).
* readers are monotone (`sexpR_mono`, `consR_mono`, `astR_mono`): in combined sessions every
  correct answer stays correct (`Silmaril.Accept.Handle.Reader.Mono.persist`).
* `listCert_sound`: a `kind`/`car`/`cdr`/`atom` chain ending in `nil` certifies a proper list of
  atoms; with `readerLang_trap_subset` every certified reader module is sound.
-/

@[expose] public section

namespace Silmaril.Formats.Api

open Silmaril.Accept.Handle

variable {α : Type} {H : Type}

theorem sexpW_hom : (sexpW α).Hom (astW (sexpSig α)) SxOp.toAST SExp.toAST :=
  Silmaril.Proofs.Formats.SExp.Api.sexpW_hom

/-- **First-class S-expression APIs are the generic AST API** at the S-expression signature. -/
theorem sexpLang_eq_astLang [DecidableEq H] {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) (T : Set (List (WEv (SxOp α) H))) :
    writerLang (astW (sexpSig α)) pol (List.map (WEv.mapOp SxOp.toAST) '' T) =
      SExp.toAST '' writerLang (sexpW α) pol T :=
  writerLang_hom sexpW_hom ha hw T

theorem sexpW_childRel : (sexpW α).ChildRel SExp.Child :=
  Silmaril.Proofs.Formats.SExp.Api.sexpW_childRel

theorem consW_childRel : (consW α).ChildRel SExp2.Child :=
  Silmaril.Proofs.Formats.SExp.Api.consW_childRel

theorem sexpLang_all_downClosed [DecidableEq H] {pol : Policy H} (hw : pol.onWrite ≠ .ub)
    {T : Set (List (WEv (SxOp α) H))} (hT : ∀ t ∈ T, ∀ e ∈ t, AllOnly e) :
    DownClosed SExp.Child (writerLang (sexpW α) pol T) :=
  writerLang_downClosed sexpW_childRel hw hT

theorem sexpR_mono : (sexpR α H).Mono := Silmaril.Proofs.Formats.SExp.Api.sexpR_mono

theorem consR_mono : (consR α H).Mono := Silmaril.Proofs.Formats.SExp.Api.consR_mono

theorem astR_mono {S : AstSig} : (astR S H).Mono := Silmaril.Proofs.Formats.SExp.Api.astR_mono

theorem consChain_sound {ρ : Env H (SExp2 α)} {hist : List (ConsQ H × ConsA α H)}
    (hf : ∀ p ∈ hist, (consR α H).valid ρ p.1 ∧ (consR α H).ok ρ p.1 p.2) {h : H}
    {as : List α} (hc : ConsChain hist h as) : ρ h = some (SExp2.ofAtoms as) :=
  Silmaril.Proofs.Formats.SExp.Api.consChain_sound hf hc

theorem listCert_sound (P : List α → Prop) :
    CertSound (consR α H) (listCert P) {x | ∃ as, x = SExp2.ofAtoms as ∧ P as} :=
  Silmaril.Proofs.Formats.SExp.Api.listCert_sound P

/-- **Certified list readers are sound** under the trapping read policy, in every environment. -/
theorem listReader_sound {P : List α → Prop} {oa : OnInvalid} (hoa : oa ≠ .ub)
    {T : Set (List (REv (ConsQ H) (ConsA α H) H))} (hT : Certified (listCert P) T)
    (Envs : Set (Env H (SExp2 α))) :
    readerLang (consR α H) .trap oa Envs T ⊆ {x | ∃ as, x = SExp2.ofAtoms as ∧ P as} :=
  readerLang_trap_subset hoa (listCert_sound P) hT Envs

end Silmaril.Formats.Api
