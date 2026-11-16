module

public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.Abstract.SessionLink.Thms
public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratLegal.Defs
import Silmaril.Proofs.Games.Abstract.SessionCat.Det
import Silmaril.Proofs.Games.Abstract.SessionCat.Assoc
import Silmaril.Proofs.Games.Abstract.SessionCat.Unit
import Silmaril.Proofs.Games.Abstract.SessionCat.Legal
import Silmaril.Proofs.Games.Abstract.SessionCat.Seq

/-!
# Session-level category laws: theorems

The laws hold on the realizable session domain: store-retaining triples whose returns are
deterministic given answers (`RetDet`) and whose servers have no plain traps (`NoPlainTrap`).
They are proved at the level of session strategies, where linking is composition with hiding
(`SessionLink.comp_threadS`), and read back on triples as observational equivalence of stores
(`StratThread.ObsEq`) by `StratSession.threadS_eq_iff`.

**Determinism of returns.** `RetDet` gives store determinism (`storeDet_of_retDet`), follows from
`AFun.Det` (`retDet_of_det`), and is preserved by linking (`retDet_linkS`), which `AFun.Det` is
not (`SessionLink.Thms`).

**Associativity** (`threadS_linkS_assoc`, `obsEq_linkS_assoc`): for a server `t`, a middle `u`
and a client `v`, the two bracketings have the same session up to the store reassociation
`((s₁, s₂), s₃) ↔ (s₁, (s₂, s₃))`, and the reassociated stores are observationally equivalent.
Hypotheses: the two servers `t` and `u` have no plain traps (`comp_threadS` needs it of the
server of each link; `linkS t u` inherits it from `u`), and all three have deterministic returns
(the stores of the four links involved are then deterministic). The equivalence of triples also
needs `NoPlainTrap v`, for `threadS_eq_iff`.

**Identity** (`threadS_idS`): the session of the identity session triple `idS` is copycat,
`DStrategy.id (sig1 A B)`, exactly (all three components, no relabelling): the forwarded answer is
returned unchanged, a trap answer being a continuing trap, so the session never ends. `idS` has
deterministic returns and no plain traps.

**Unit laws** (`threadS_linkS_idS`, `threadS_idS_linkS`, `obsEq_linkS_idS`, `obsEq_idS_linkS`):
linking with `idS` on either side gives the same session, the unit store `PUnit` being added, and
observationally equivalent stores. Hypotheses: `RetDet` of the other component, and `NoPlainTrap`
of it when it is the server (`linkS t idS`) or for the equivalence of triples.

**Legality** (no hypotheses beyond legality itself):

* `legal_linkS`: the import logs of `linkS t u` are made of logs of the server (the client's calls
  are hidden), so a legal server gives a legal linked triple, whatever the client;
* `ansLegal_linkS`: the answers of `linkS t u` are the client's;
* `logLegal_served`: when the server's answers are legal for the client's interface
  (`AnsLegal L₁ t`), every client call it serves is legal; hence `linkS_legalPart`: linking only
  exercises the legal part of the (saturated) client, `linkS t (legalPart L₁ (sat u)) = linkS t u`.
  Saturation is used: a pending call of `u` after an illegal answer forces an earlier call
  prefix with a legal log, which `legalPart L₁ u` drops with the pending call;
* `legal_pairS`, `ansLegal_pairS`: pairing preserves both, the answers being relabelled
  (`pairAns`);
* `toDStratL_legalPart`: the legal play object of `StratLegal` sees only the legal part,
  `StratLegal.toDStratL L (legalPart L t) = StratLegal.toDStratL L t`.

**Sequencing within a round** (no hypotheses): `mem_seqS` — a continuing trap of the first part
aborts the round keeping its store, a plain trap or divergence is kept, and a value continues with
the second part; `seqS_assoc`, `seqS_retS`, `retS_seqS` — associativity and units. **Store
strength** (no hypotheses): `frameS` preserves sequencing and its unit (`frameS_seqS`,
`frameS_retS`), and the underlying operations (`frameS_seqT`, `frameS_pureT`, `frameS_mapT`,
`frameS_caseT`).
-/

public section

namespace Silmaril.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}}

/-! ## Determinism of returns -/

/-- **Deterministic returns give deterministic stores.** -/
theorem storeDet_of_retDet {S A B : Type u} {t : ObsTriple E S A B} (ht : RetDet t) :
    StoreDet t :=
  Silmaril.Proofs.Games.Abstract.SessionCat.storeDet_of_retDet ht

/-- Determinism given answers gives deterministic returns. -/
theorem retDet_of_det {S A B : Type u} {t : ObsTriple E S A B} (ht : AFun.Det t.1) : RetDet t :=
  fun _ _ _ _ _ _ _ _ h₁ h₂ => ht _ _ _ _ h₁ h₂

/-- **Linking preserves deterministic returns.** -/
theorem retDet_linkS {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})} (ht : RetDet t) (hu : RetDet u) :
    RetDet (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.retDet_linkS ht hu

/-! ## Associativity -/

section Assoc

variable {S₁ S₂ S₃ A B A' B' A'' B'' : Type u} {t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1})}
  {v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1})}

/-- **Linking is associative on sessions**, up to the store reassociation. -/
theorem threadS_linkS_assoc (hnt : NoPlainTrap t) (hnu : NoPlainTrap u) (ht : RetDet t)
    (hu : RetDet u) (hv : RetDet v) (s₁ : S₁) (s₂ : S₂) (s₃ : S₃) :
    threadS (linkS (linkS t u) v) ((s₁, s₂), s₃) = threadS (linkS t (linkS u v)) (s₁, (s₂, s₃)) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.threadS_linkS_assoc hnt hnu ht hu hv s₁ s₂ s₃

/-- **Linking is associative on triples**, up to observational equivalence of the reassociated
stores. -/
theorem obsEq_linkS_assoc (hnt : NoPlainTrap t) (hnu : NoPlainTrap u) (hnv : NoPlainTrap v)
    (ht : RetDet t) (hu : RetDet u) (hv : RetDet v) (s₁ : S₁) (s₂ : S₂) (s₃ : S₃) :
    ObsEq (linkS (linkS t u) v) (linkS t (linkS u v)) ((s₁, s₂), s₃) (s₁, (s₂, s₃)) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.obsEq_linkS_assoc hnt hnu hnv ht hu hv s₁ s₂ s₃

end Assoc

/-! ## Identity and units -/

/-- **The identity session is copycat.** -/
theorem threadS_idS {A B : Type u} :
    threadS (idS (A := A) (B := B)) PUnit.unit = DStrategy.id (sig1 A B) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.threadS_idS

/-- The identity session has deterministic returns. -/
theorem retDet_idS {A B : Type u} : RetDet (idS (A := A) (B := B)) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.retDet_idS

/-- The identity session has no plain traps. -/
theorem noPlainTrap_idS {A B : Type u} : NoPlainTrap (idS (A := A) (B := B)) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.noPlainTrap_idS

section Unit

variable {S A B A' B' : Type u}

/-- **Right unit on sessions**: a server served to the identity client. -/
theorem threadS_linkS_idS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (hnt : NoPlainTrap t)
    (ht : RetDet t) (s : S) : threadS (linkS t idS) (s, PUnit.unit) = threadS t s :=
  Silmaril.Proofs.Games.Abstract.SessionCat.threadS_linkS_idS hnt ht s

/-- **Left unit on sessions**: a client served by the identity server. -/
theorem threadS_idS_linkS {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})} (hu : RetDet u)
    (s : S) : threadS (linkS idS u) (PUnit.unit, s) = threadS u s :=
  Silmaril.Proofs.Games.Abstract.SessionCat.threadS_idS_linkS hu s

/-- **Right unit on triples**, up to observational equivalence. -/
theorem obsEq_linkS_idS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (hnt : NoPlainTrap t)
    (ht : RetDet t) (s : S) : ObsEq (linkS t idS) t (s, PUnit.unit) s :=
  Silmaril.Proofs.Games.Abstract.SessionCat.obsEq_linkS_idS hnt ht s

/-- **Left unit on triples**, up to observational equivalence. -/
theorem obsEq_idS_linkS {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})}
    (hnu : NoPlainTrap u) (hu : RetDet u) (s : S) : ObsEq (linkS idS u) u (PUnit.unit, s) s :=
  Silmaril.Proofs.Games.Abstract.SessionCat.obsEq_idS_linkS hnu hu s

end Unit

/-! ## Legality -/

section Legal

variable {L : (m : E.Op) → E.Ar m → Prop} {S S' A B A' B' : Type u}
  {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- **Linking with a legal server is legal.** -/
theorem legal_linkS (ht : Legal L t) : Legal L (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.legal_linkS ht

/-- **The answers of a linked triple are the client's.** -/
theorem ansLegal_linkS {L' : A' → B' ⊕ PUnit.{u + 1} → Prop} (hu : AnsLegal L' u) :
    AnsLegal L' (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.ansLegal_linkS hu

/-- **A server with legal answers serves legal calls.** -/
theorem logLegal_served {L₁ : A → B ⊕ PUnit.{u + 1} → Prop} (ht : AnsLegal L₁ t) {s s₁ : S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} (h : Rounds t s rs s₁) :
    LogLegal (E := sig1 A B) L₁ (SessionLink.served rs) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.logLegal_served ht h

/-- **Linking exercises only the legal part of the client**, for a server with legal answers. -/
theorem linkS_legalPart {L₁ : A → B ⊕ PUnit.{u + 1} → Prop} (ht : AnsLegal L₁ t) :
    linkS t (legalPart (E := sig1 A B) L₁ (sat u)) = linkS t u :=
  Silmaril.Proofs.Games.Abstract.SessionCat.linkS_legalPart ht

/-- **The legal play object sees only the legal part.** -/
theorem toDStratL_legalPart {A₀ B₀ : Type u} (v : ObsTriple E S A₀ B₀) :
    StratLegal.toDStratL L (legalPart L v) = StratLegal.toDStratL L v :=
  congrArg StratObs.toDStrat (Silmaril.Proofs.Games.Abstract.SessionCat.restrict_legalPart v)

variable {S₁ S₂ A₁ A₂ B₁ B₂ : Type u} {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
  {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}

/-- **Pairing legal triples is legal.** -/
theorem legal_pairS (h₁ : Legal L t₁) (h₂ : Legal L t₂) : Legal L (pairS t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.legal_pairS h₁ h₂

/-- **Pairing triples with legal answers has legal answers.** -/
theorem ansLegal_pairS {L₁ : A₁ → B₁ ⊕ PUnit.{u + 1} → Prop} {L₂ : A₂ → B₂ ⊕ PUnit.{u + 1} → Prop}
    (h₁ : AnsLegal L₁ t₁) (h₂ : AnsLegal L₂ t₂) : AnsLegal (pairAns L₁ L₂) (pairS t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.ansLegal_pairS h₁ h₂

end Legal

/-! ## Sequencing and strength -/

section Seq

open StratOps

variable {S S' A B C D : Type u}

/-- **A round of a sequence**: a plain trap or divergence of `t`, a continuing trap of `t`
(aborting the round, keeping its store), or a value of `t` continued by `u`. -/
theorem mem_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})}
    {s : S} {a : A} {x : List (Call E) × End S (C ⊕ PUnit.{u + 1})} :
    x ∈ (seqS t u).1 s a ↔ (∃ c, (c, End.trap) ∈ t.1 s a ∧ x = (c, End.trap)) ∨
      (∃ c, (c, End.div) ∈ t.1 s a ∧ x = (c, End.div)) ∨
      (∃ c s₁, (c, End.ret (.inr PUnit.unit) s₁) ∈ t.1 s a ∧
        x = (c, End.ret (.inr PUnit.unit) s₁)) ∨
      ∃ c₁ b s₁ c₂ e, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, e) ∈ u.1 s₁ b ∧
        x = (c₁ ++ c₂, e) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.mem_seqS

/-- **Session sequencing is associative.** -/
theorem seqS_assoc (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S B (C ⊕ PUnit.{u + 1})) (v : ObsTriple E S C (D ⊕ PUnit.{u + 1})) :
    seqS (seqS t u) v = seqS t (seqS u v) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.seqS_assoc t u v

/-- `retS` is a right unit. -/
theorem seqS_retS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : seqS t retS = t :=
  Silmaril.Proofs.Games.Abstract.SessionCat.seqS_retS t

/-- `retS` is a left unit. -/
theorem retS_seqS (u : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : seqS retS u = u :=
  Silmaril.Proofs.Games.Abstract.SessionCat.retS_seqS u

/-- **Strength preserves sequencing of triples.** -/
theorem frameS_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) :
    frameS S' (seqT t u) = seqT (frameS S' t) (frameS S' u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_seqT t u

/-- Strength preserves the identity. -/
theorem frameS_pureT : frameS S' (pureT : ObsTriple E S A A) = pureT :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_pureT

/-- Strength commutes with pure maps. -/
theorem frameS_mapT (t : ObsTriple E S A B) (h : B → C) :
    frameS S' (mapT t h) = mapT (frameS S' t) h :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_mapT t h

/-- Strength commutes with copairing. -/
theorem frameS_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    frameS S' (caseT t u) = caseT (frameS S' t) (frameS S' u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_caseT t u

/-- **Strength preserves the unit of session sequencing.** -/
theorem frameS_retS : frameS S' (retS : ObsTriple E S A (A ⊕ PUnit.{u + 1})) = retS :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_retS

/-- **Strength preserves session sequencing.** -/
theorem frameS_seqS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S B (C ⊕ PUnit.{u + 1})) :
    frameS S' (seqS t u) = seqS (frameS S' t) (frameS S' u) :=
  Silmaril.Proofs.Games.Abstract.SessionCat.frameS_seqS t u

end Seq

end Silmaril.Games.Abstract.SessionCat
