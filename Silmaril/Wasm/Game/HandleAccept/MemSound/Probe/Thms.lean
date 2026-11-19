module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Probe.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.Live

/-!
# The probe reader: soundness and non-vacuity at every reader API and atom payload

* `probeLang_subset` (**the probe reader bridge**, any reader `Rd`): with the reader contract
  (`probeContract`: accepts name members of `L`, every decoded read is valid and correct in
  `ρ`) proved in every fixed environment, the reader language under the trapping read policy
  is included in `L`, for every accept policy without undefined behaviour and every set of fixed
  environments.
* **Soundness**, for every profile, every atom type `α` and every payload decoder `pay`, against
  every host admitted by `probeReply` (keeps the code, may rewrite any memory contents at every
  answer, one `i32` from `next`, nothing from `leaf` and `accept`):
  `nary_sound` (`sexpR α`: only lists whose first child is an atom, `firstAtoms`),
  `cons_sound` (`consR α`: only pairs whose car is an atom, `carAtoms`),
  `ast_sound` (`astR (sexpSig α)`: only nodes whose first child is a leaf, `firstLeaves`).
* **Non-vacuity** (`nary_live`, `cons_live`, `ast_live`): when the payload reads `x` on every
  page the host `probeEnv 2 w` writes, the one-element list `(x)`, the pair `(x . nil)` and the
  node with the one leaf `x` are accepted over all fixed environments.
* **Payloads on that page**: `bytesPay_page` (the `list<u8>` is the two low bytes `b₀ b₁` of
  `w`), `kindPay_page` (with `w = k < 256`: the bytes `k 0` of kind code `k`), `hintPay_page`
  (with `w = 4`: the octets `4 0` with the hint `2 0 0 0`), `u64Pay_page` (the `u64` at `0` is
  `8 + 2 * 2 ^ 32`).

The upper bounds are one Hoare-logic proof of `probeMod`, generic in the reader, the decoder
and the contract's facts (`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.probe_sat`);
the lower bounds one traced session, generic in the decoder (`probe_traces`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Probe

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live

variable {Q A Y α : Type}

/-- **The probe reader bridge.** -/
theorem probeLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {m : Module} {Rd : Reader Q A (BitVec 32) Y} {d : ProbeDec Q A} {L : Set Y}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (probeRoles d) (probeContract Rd d ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) Y)) :
    probeLang P Envs memIdx m Rd d .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.probeLang_subset hsat hE hoa Rhos

/-- **The n-ary probe accepts only lists whose first child is an atom.** -/
theorem nary_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp α))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx) (sexpR α (BitVec 32))
      (naryProbe pay) .trap oa Rhos ⊆ firstAtoms α :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.nary_sound P pay hoa Rhos

/-- **The cons probe accepts only pairs whose car is an atom.** -/
theorem cons_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 α))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx) (consR α (BitVec 32))
      (consProbe pay) .trap oa Rhos ⊆ carAtoms α :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.cons_sound P pay hoa Rhos

/-- **The AST probe accepts only nodes whose first child is a leaf.** -/
theorem ast_sound (P : Profile) (pay : Payload α) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) (AST (sexpSig α)))) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx) (astR (sexpSig α) (BitVec 32))
      (astProbe pay) .trap oa Rhos ⊆ firstLeaves α :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.ast_sound P pay hoa Rhos

/-- **The n-ary probe accepts `(x)`** when its payload reads `x` on the written page. -/
theorem nary_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    SExp.ofList [.atom x] ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod naryIx)
      (sexpR α (BitVec 32)) (naryProbe pay) .trap oa Set.univ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.nary_live P oa pay w hA

/-- **The cons probe accepts `(x . nil)`** when its payload reads `x` on the written page. -/
theorem cons_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    SExp2.cons (.atom x) .nil ∈ probeLang P (ReplyEnvs probeReply) 0 (probeMod consIx)
      (consR α (BitVec 32)) (consProbe pay) .trap oa Set.univ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.cons_live P oa pay w hA

/-- **The AST probe accepts the node with one leaf `x`** when its payload reads `x` on the
written page. -/
theorem ast_live (P : Profile) (oa : OnInvalid) (pay : Payload α) (w : BitVec 32) {x : α}
    (hA : ∀ B B', B.size = 65536 → itemsBytes w w B = some B' →
      pay ⟨.values [], some B'⟩ 0 = some x) :
    AST.node (S := sexpSig α) SxTag.branch () [AST.node (S := sexpSig α) SxTag.leaf x []] ∈
      probeLang P (ReplyEnvs probeReply) 0 (probeMod astIx) (astR (sexpSig α) (BitVec 32))
        (astProbe pay) .trap oa Set.univ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.ast_live P oa pay w hA

/-- The `list<u8>` on the written page is the two low bytes of `w`. -/
theorem bytesPay_page (dec : List UInt8 → Option α) (b₀ b₁ : UInt8) {B B' : ByteArray}
    (hB : B.size = 65536)
    (hw : itemsBytes (BitVec.ofNat 32 (b₀.toNat + 256 * b₁.toNat))
      (BitVec.ofNat 32 (b₀.toNat + 256 * b₁.toNat)) B = some B') :
    bytesPay dec ⟨.values [], some B'⟩ 0 = dec [b₀, b₁] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.bytesPay_page dec b₀ b₁ hB hw

/-- The kind-tagged `list<u8>` on the page written with `w = kindCode k`: the bytes `k 0` with
the kind code `k`. -/
theorem kindPay_page (dec : BitVec 32 → List UInt8 → Option α) (k : UInt8) {B B' : ByteArray}
    (hB : B.size = 65536) (hw : itemsBytes (kindCode k) (kindCode k) B = some B') :
    kindPay dec ⟨.values [], some B'⟩ 0 = dec (kindCode k) [k, 0] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.kindPay_page dec k hB hw

/-- The hinted atom on the page written with `w = 4`: the octets `4 0` with the hint
`2 0 0 0`. -/
theorem hintPay_page {B B' : ByteArray} (hB : B.size = 65536) (hw : itemsBytes 4 4 B = some B') :
    hintPay ⟨.values [], some B'⟩ 0 = some (some [2, 0, 0, 0], [4, 0]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.hintPay_page hB hw

/-- The `u64` at `0` on the written page is `8 + 2 * 2 ^ 32`. -/
theorem u64Pay_page (w : BitVec 32) {B B' : ByteArray} (hB : B.size = 65536)
    (hw : itemsBytes w w B = some B') :
    u64Pay ⟨.values [], some B'⟩ 0 = some (8 + 2 * 2 ^ 32) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe.u64Pay_page w hB hw

end Silmaril.Wasm.Game.HandleAccept.MemSound.Probe
