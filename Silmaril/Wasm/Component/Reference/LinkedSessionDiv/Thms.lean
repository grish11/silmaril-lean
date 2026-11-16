module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Main

/-!
# Diverging calls of linked sessions: theorems

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`) answering every import of the
importer B (`l.imp`), under `Linked2.Adequate`. Every profile `P`, component choice profile
`prof`, host implementation `impl` and host state `h₀`; the reference component is `l.toRef` on
`core3P P` under `linkHost impl`.

* **Specification divergence is reference divergence** (`Linked2.divSpecToRef`, proved, no extra
  hypothesis): `Linked2.DivSpecToRef P prof l`, i.e. `sessDivs ⊆ refDivs`. After a specification
  session, a round that never answers, for any of its three sources, is a diverging top-level
  call of the reference machine after the reference images of the session's outcomes.
  The typing hypotheses of `DivSpecToRef` are not needed: `DivRound.Ok` checks the arguments.

**The three sources** are the three divergent ends of a round of the H2 owner's linked triple
`Games.Abstract.SessionLink.linkS` (#706): the client diverges (`Linked2.DivB`), the server
diverges inside a served call (`Linked2.DivA`), the client makes infinitely many served calls
(`Linked2.Chatter`, the hidden chatter of `DStrategy.comp`). The formal correspondence to
`comp_threadS` is not stated here. On the machine:

* the session prefix is #712's forward run (`linkCall_fwd` per round, `resumeCfg` after a trap);
* the round's prefix up to the point of divergence is a prefix variant of `rounds_fwd`
  (`roundsPre_fwd`, ending at `.running`); if an import call of the prefix was answered by a
  trap, B's thread is filled with a trap, and none of the sources applies (it never calls out
  again, and it does not run forever: its code shrinks, `Wasm.Game.trapped_step_lt`);
* **(i)** B's infinite host-free Core run maps step for step to an infinite run of B's core
  activation (`link_inf`, as `coreTrace_of_divAt` for `Simple`);
* **(ii)** B runs to the callout, the nested `canon lower`/`canon lift` enters A (`nest_atTS`),
  and A's infinite Core run from its store maps step for step to the nested activation;
* **(iii)** each served import call is a nonempty machine run back into B's core activation
  (`exp_fwd` through `LInv.resume_fwd`, and B's segment between callouts); the segments are
  concatenated by a coinduction whose productivity is their nonemptiness.

**Not claimed.**

* The converse `refDivs ⊆ sessDivs` is proved in `Reference.LinkedSessionDivInv`
  (`Linked2.divRefToSpec`, hence `Linked2.sessDivs_eq_refDivs`): a machine divergence inside a
  linked call stays in B's core activation, diverges in A's, or crosses the link infinitely
  often.
* Host observations: within `Linked2`, `l.toRef` has no host imports; a parent passing host
  imports to B (`linkedHRef`) is not covered.
* Productive (infinite) linked executions come next, through `mem_inf_linkS_iff_of_det` (#706).
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.{Core, Round, Call, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Numerics (Profile)

/-- **Specification divergence of a linked session is reference divergence** (proved, every
profile and component choice profile, under every host): for an adequate linked component, every
diverging session call of the specification (`sessDivs`: B diverges host-free, A diverges inside
an import call, or B makes infinitely many served import calls) is one of the reference machine
(`refDivs`). -/
theorem Linked2.divSpecToRef (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate) :
    Linked2.DivSpecToRef P prof l :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.linked2_divSpecToRef P prof l hl

end Silmaril.Wasm.Component.Reference
