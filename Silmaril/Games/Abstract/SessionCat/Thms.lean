module

public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.Abstract.SessionLink.Thms
import Silmaril.Proofs.Games.Abstract.SessionCat.Det
import Silmaril.Proofs.Games.Abstract.SessionCat.Assoc
import Silmaril.Proofs.Games.Abstract.SessionCat.Unit

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

end Silmaril.Games.Abstract.SessionCat
