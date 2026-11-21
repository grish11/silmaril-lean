module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasm.Component.Reference.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Typed.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref

open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable {E : CoreEngine}

theorem acceptedExportTyped_acceptedExport [∀ a b, Decidable (E.ExternSub a b)]
    {prof : ProfileKind} {c : Syntax.Component E.Module} {w : List UInt8}
    (h : AcceptedExportTyped prof c w) : AcceptedExport prof c w :=
  let ⟨m₁, inst, es, f, _, hi, hf, _, _, _, hc⟩ := h
  Or.inl ⟨m₁, inst, es, f, hi, hf, hc⟩

variable [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem bytesOf?_bytesVal (w : List UInt8) : bytesOf? [bytesVal w] = some w := by
  have h : ∀ b : UInt8, u8Of? (.int .u8 (b.toNat : Int)) = some b := by
    intro b
    have hb := b.toNat_lt
    have hc : (0:Int) ≤ ↑b.toNat ∧ (↑b.toNat : Int) < 256 := ⟨by omega, by omega⟩
    simp only [u8Of?, hc, and_self, ↓reduceIte, Int.toNat_natCast, Option.some.injEq]
    exact UInt8.ofNat_toNat
  simp only [bytesOf?, bytesVal]
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.mapM_cons, List.map_cons, h b] at ih ⊢
    simp [ih]

theorem acceptedTyped_bytes {prof : ProfileKind} {c : Syntax.Component E.Module}
    {w : List UInt8} (h : AcceptedTyped prof c w) : AcceptedTypedBytes acceptFT prof c w :=
  ⟨[bytesVal w], h, bytesOf?_bytesVal w⟩

theorem acceptedExportTyped_of_run {fuel fuel' : Nat} {c : Syntax.Component E.Module}
    {w : List UInt8} {r₁ : RunResult E AcceptSt o.State} {inst : InstId}
    {es : List (String × FuncId)} {f : FuncId} {ft : WIT.FuncType Empty RtId}
    {r : RunResult E AcceptSt o.State}
    (hi : (emb X).instantiateRun o fuel c [] (Silmaril.Wasm.Component.Reference.initConfig []) =
      some (r₁, inst, es))
    (hf : es.lookup "accept" = some f) (hft : funcFT? r₁.config f = some ft)
    (hty : argsTyped ft [bytesVal w] = true) (hres : ft.result = some (.prim .bool))
    (hc : (emb X).callTop o fuel' ⟨0⟩ f [bytesVal w] r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some (.resolved (some [.bool true]))) :
    AcceptedExportTyped o.prof c w :=
  ⟨r₁.config, inst, es, f, ft, Silmaril.Wasm.Component.Reference.instantiateRun_mem (emb X) o hi,
    hf, hft, hty, hres, Silmaril.Wasm.Component.Reference.callTop_mem (emb X) o hc ho⟩

end Silmaril.Proofs.Wasi.Component.Accept.Ref
