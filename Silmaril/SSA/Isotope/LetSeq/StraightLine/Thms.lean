module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Coverage
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Reflection
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.PureAssembly
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.ProductReflection
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Separation

/-! # Trace reflection for native open LetSeq terms -/

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)

/-- Replay uses native `bindPair`, pure let β and congruence. -/
theorem Admitted.replay {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (p : Admitted β t) : Equiv false Γ₀ β t p.normal Atom :=
  replay_proof p

/-- Run one request, then bind the two reply coordinates in native order. -/
theorem run_request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
    (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body)
    (ρ : BoundEnv Value β) :
    run (canonicalDerivation (.request f x y rest)) ρ =
      model.eval f (x.value ρ, y.value ρ) >>= fun ab =>
        run (canonicalDerivation rest) ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) :=
  run_request_proof f x y rest ρ

theorem mem_request_trace {A : Type} {f : Request} {arg : Nat × Nat} {k : Nat × Nat → Trace A}
    {z : A} {w : Log} :
    (z, w) ∈ (model.eval f arg >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, arg, reply⟩ * tail = w :=
  request_mem_proof

/-- A separating environment suffices. Fresh reply coordinates chosen in
one legal trace then separate all retained input and reply projections. -/
theorem run_eq_iff_normal {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    run d ρ = run e ρ ↔ p.normal = q.normal :=
  run_eq_iff_normal_proof p q d e ρ fresh sep

theorem native_iff_normal {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    Equiv false Γ₀ β t u Atom ↔ p.normal = q.normal :=
  native_iff_normal_proof p q d e ρ fresh sep

/-- The existing typed embedding preserves and reflects native equations on
the admitted slice with a separating input environment. -/
theorem embed_iff_native {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    LetCase.LocallyNameless.Equiv false Γ₀ β (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) Atom ↔
      Equiv false Γ₀ β t u Atom :=
  embed_iff_native_proof p q d e ρ fresh sep

theorem entry_run {body : Term 3} {A : Types}
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) body A) (x y : Nat) :
    run (entry d) (packetEnv (x, y)) =
      run d (((packetEnv (x, y)).snoc (A := Atom) x).snoc (A := Atom) y) :=
  entry_run_proof d x y

theorem entry_run_eq_iff_normal {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔ p.normal = q.normal :=
  entry_iff_normal_proof p q d e

/-- The concrete point `(0, 1)` separates the actual open packet terms. -/
theorem entry_run_eq_iff_native {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom :=
  entry_iff_native_proof p q d e

/-- Native LetCase equivalence of the actual embedded packet terms is
equivalent to native LetSeq equivalence. -/
theorem entry_embed_iff_native {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    LetCase.LocallyNameless.Equiv false Γ₀ input
      (Morphism.SeqCase.embed (.let₂ (.bv 0) t)) (Morphism.SeqCase.embed (.let₂ (.bv 0) u)) Atom ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom :=
  entry_embed_iff_native_proof p q d e

/-- Pure assembly contributes its value and the empty trace. -/
theorem Assembly.run_eq_pure {n : Nat} {β : BoundCtx Types n} {A : Types}
    (v : Assembly β A) (ρ : BoundEnv Value β) : run v.derivation ρ = pure (v.value ρ) :=
  assembly_run_proof v ρ

/-- The assembled argument is evaluated before the request, whose reply is
bound once in left-to-right order. -/
theorem run_product_step {n : Nat} {β : BoundCtx Types n} {A : Types} {body : Term (n + 2)}
    (f : Request) (arg : Assembly β Packet)
    (rest : ProductCanonical ((β.snoc Atom).snoc Atom) body A) (ρ : BoundEnv Value β) :
    run (ProductCanonical.derivation (.step f arg rest)) ρ =
      model.eval f (arg.value ρ) >>= fun ab =>
        run rest.derivation ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) :=
  run_step_proof f arg rest ρ

/-- In an atomic context, any native pure derivation is an admitted
assembly, using the identity slot substitution. -/
def PureAssembly.ofAtomic {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (d : Derivation Request Γ₀ β t A) (h : LocallyNameless.Pure false t)
    (slots : ∀ i, β.get i = Atom) : PureAssembly β t A :=
  pureAssemblyOfAtomic d h slots

/-- Replay native pure assembly, including lets and product elimination, to a
variable, unit and pair tree. -/
theorem PureAssembly.normalizes {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (p : PureAssembly β t A) : ∃ v : Assembly β A, Equiv false Γ₀ β t v.term A :=
  assembly_normalize_proof p

/-- Replay pure argument and result assembly while preserving the order of the
effectful request binders. -/
theorem ProductProgram.normalizes {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (p : ProductProgram β t A) :
    ∃ u : Term n, ∃ _ : ProductCanonical β u A, Equiv false Γ₀ β t u A :=
  product_normalize_proof p

/-- A separating environment suffices for reflection at any admitted
structural result type. -/
theorem product_run_eq_iff_native {n : Nat} {β : BoundCtx Types n} {A : Types} {t u : Term n}
    (p : ProductProgram β t A) (q : ProductProgram β u A)
    (d : Derivation Request Γ₀ β t A) (e : Derivation Request Γ₀ β u A)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    run d ρ = run e ρ ↔ Equiv false Γ₀ β t u A :=
  product_run_iff_native_proof p q d e ρ fresh sep

theorem product_embed_iff_native {n : Nat} {β : BoundCtx Types n} {A : Types} {t u : Term n}
    (p : ProductProgram β t A) (q : ProductProgram β u A)
    (d : Derivation Request Γ₀ β t A) (e : Derivation Request Γ₀ β u A)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    LetCase.LocallyNameless.Equiv false Γ₀ β (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) A ↔
      Equiv false Γ₀ β t u A :=
  product_embed_iff_native_proof p q d e ρ fresh sep

/-- Reflection for actual open product-input terms at the separating point
`(0, 1)`. -/
theorem entry_product_run_eq_iff_native {t u : Term 3} {A : Types}
    (p : ProductProgram ((input.snoc Atom).snoc Atom) t A)
    (q : ProductProgram ((input.snoc Atom).snoc Atom) u A)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t A)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u A) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) A :=
  entry_product_run_iff_native_proof p q d e

theorem entry_product_embed_iff_native {t u : Term 3} {A : Types}
    (p : ProductProgram ((input.snoc Atom).snoc Atom) t A)
    (q : ProductProgram ((input.snoc Atom).snoc Atom) u A)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t A)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u A) :
    LetCase.LocallyNameless.Equiv false Γ₀ input
      (Morphism.SeqCase.embed (.let₂ (.bv 0) t)) (Morphism.SeqCase.embed (.let₂ (.bv 0) u)) A ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) A :=
  entry_product_embed_iff_native_proof p q d e

/-- Normalize any exact derivation after supplying assemblies for its input
variables. The bound variable and unit cases give pure assemblies. The
primitive case sequences argument effects before the request. The pair case
sequences left before right. Both let constructors thread their result into
the continuation, with product destructuring substituting both fields.
Named free variables are absent in this signature. -/
theorem normalize_exact {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    {t : Term n} {A : Types} (d : Derivation Request Γ₀ source t A)
    (σ : AssemblyEnv source target) : ProductNormalizes target (t.bsubst σ.terms) A :=
  normalize_exact_proof d σ

/-- Every exactly typed term at the native packet boundary is equivalent to
destructuring its input followed by an existing `ProductProgram`.
This includes whole-packet uses and arbitrary effectful nesting. -/
theorem packet_program {t : Term 1} {A : Types} (d : Derivation Request Γ₀ input t A) :
    ∃ u : Term 3, ∃ _ : ProductProgram ((input.snoc Atom).snoc Atom) u A,
      Equiv false Γ₀ input t (.let₂ (.bv 0) u) A :=
  packet_program_proof d

/-- Reflection at the fixed packet boundary requires only the exact typings. -/
theorem packet_run_eq_iff_native {t u : Term 1} {A : Types}
    (d : Derivation Request Γ₀ input t A) (e : Derivation Request Γ₀ input u A) :
    run d (packetEnv (0, 1)) = run e (packetEnv (0, 1)) ↔ Equiv false Γ₀ input t u A :=
  packet_run_iff_native_proof d e

theorem packet_embed_iff_native {t u : Term 1} {A : Types}
    (d : Derivation Request Γ₀ input t A) (e : Derivation Request Γ₀ input u A) :
    LetCase.LocallyNameless.Equiv false Γ₀ input (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) A ↔
      Equiv false Γ₀ input t u A :=
  packet_embed_iff_native_proof d e

end Silmaril.Isotope.LetSeq.StraightLine
