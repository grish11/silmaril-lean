module

public import Silmaril.Wasm.Game.HandleAccept.Families.Mixed.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed

namespace Silmaril.Wasm.Game.HandleAccept.Families.Mixed

open Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

/-- The decoded symbol/string replay accepts the list, not just its allocated leaves. -/
public theorem symbol_string_accepted :
    SExp.ofList [.atom symbolA, .atom stringB] ∈
      writerLang (sexpW (Fam.Atom .symStrKwBytes)) {}
        {trace | some trace = mixedPairReplay "symbol" "string"} := by
  simpa only [symbol_string_trace, Option.some.injEq, Set.ofPred_eq_eq_singleton] using
    Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed.pair_accepted symbolA stringB

/-- The two other atom kinds take the same list path through the family table. -/
public theorem blob_keyword_accepted :
    SExp.ofList [.atom blobA, .atom keywordB] ∈
      writerLang (sexpW (Fam.Atom .symStrKwBytes)) {}
        {trace | some trace = mixedPairReplay "blob" "keyword"} := by
  simpa only [blob_keyword_trace, Option.some.injEq, Set.ofPred_eq_eq_singleton] using
    Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed.pair_accepted blobA keywordB

/-- The AST writer accepts the same mixed list with its typed leaf payloads. -/
public theorem symbol_string_ast_accepted :
    SExp.toAST (SExp.ofList [.atom symbolA, .atom stringB]) ∈
      writerLang (astW (sexpSig (Fam.Atom .symStrKwBytes))) ({} : Policy (BitVec 32))
        (List.map (WEv.mapOp SxOp.toAST) '' {trace | some trace = mixedPairReplay "symbol" "string"}) := by
  rw [sexpLang_eq_astLang (by decide) (by decide)]
  exact Set.mem_image_of_mem _ symbol_string_accepted

/-- Both cons cells resolve their real handles; the tagged head retains its hint. -/
public theorem hinted_cons_accepted : hintedConsTree ∈
    writerLang (consW Hinted) {} {trace | some trace = hintedConsReplay} := by
  simpa only [hinted_cons_trace, Option.some.injEq, Set.ofPred_eq_eq_singleton] using
    Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed.hinted_cons_accepted

end Silmaril.Wasm.Game.HandleAccept.Families.Mixed
