module

public import Silmaril.Logic.Smt.SExpr.Writer.Defs
public import Mathlib.Data.List.Basic

@[expose] public section
namespace Silmaril.Logic.Smt.SExpr.Writer

private theorem byte_roundtrip {c : Char} (h : LegalChar c) :
    (UInt8.ofNat c.toNat).toNat = c.toNat := by
  apply UInt8.toNat_ofNat_of_lt'
  have hc : c.toNat < 128 := h.2.1
  change c.toNat < 256
  omega

/-- Ordinary atom bytes extend the reversed token buffer without touching the
accumulated tokens. The continuation may contain arbitrary reader input. -/
theorem lex_chars (cs : List Char) (hcs : ∀ c ∈ cs, LegalChar c)
    (tail : List UInt8) (cur : List Char) (acc : List Tok) :
    lex (cs.map (fun c => UInt8.ofNat c.toNat) ++ tail) false cur acc =
      lex tail false (cs.reverse ++ cur) acc := by
  induction cs generalizing cur with
  | nil => rfl
  | cons c cs ih =>
      have hc : LegalChar c := hcs c (by simp)
      have hrest : ∀ d ∈ cs, LegalChar d := fun d hd => hcs d (by simp [hd])
      have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := byte_roundtrip hc
      have h33 : 33 ≤ c.toNat := hc.1
      have h128 : c.toNat < 128 := hc.2.1
      rcases hc with ⟨_, _, h34, h40, h41, h59, h124⟩
      simp only [List.map_cons, List.cons_append, lex, hb]
      have hspace : c.toNat ≠ 32 := by omega
      have htab : c.toNat ≠ 9 := by omega
      have hlf : c.toNat ≠ 10 := by omega
      have hcr : c.toNat ≠ 13 := by omega
      have hcontrol : ¬ c.toNat < 32 := by omega
      have hhigh : ¬ c.toNat ≥ 128 := by omega
      simpa [h59, h40, h41, hspace, htab, hlf, hcr, hcontrol, hhigh, h34, h124,
        List.reverse_cons, List.append_assoc] using ih hrest (c :: cur)

/-- One emitted atom and its separator flush exactly one lexer token. -/
theorem lex_atom {s : String} (hs : LegalAtom s) (tail : List UInt8) (acc : List Tok) :
    lex (atomBytes s ++ 32 :: tail) false [] acc =
      lex tail false [] (.atom s :: acc) := by
  rw [atomBytes, lex_chars s.toList hs.2]
  simp [lex, flush, hs.1]

def LegalToken : Tok → Prop
  | .atom s => LegalAtom s
  | _ => True

/-- Emitted token prefixes preserve arbitrary lexer continuations and reversed
accumulators. No acceptance assumption is made about the continuation. -/
theorem lex_tokens (ts : List Tok) (hts : ∀ t ∈ ts, LegalToken t)
    (tail : List UInt8) (acc : List Tok) :
    lex (renderTokens ts ++ tail) false [] acc =
      lex tail false [] (ts.reverse ++ acc) := by
  induction ts generalizing acc with
  | nil => simp [renderTokens]
  | cons t ts ih =>
      have ht : LegalToken t := hts t (by simp)
      have hrest : ∀ u ∈ ts, LegalToken u := fun u hu => hts u (by simp [hu])
      cases t with
      | atom s =>
        simpa [renderTokens, tokenBytes, List.append_assoc, List.reverse_cons] using
          (lex_atom ht (renderTokens ts ++ tail) acc).trans (ih hrest (.atom s :: acc))
      | lp =>
        simpa [renderTokens, tokenBytes, lex, flush, List.reverse_cons, List.append_assoc]
          using ih hrest (.lp :: acc)
      | rp =>
        simpa [renderTokens, tokenBytes, lex, flush, List.reverse_cons, List.append_assoc]
          using ih hrest (.rp :: acc)

private def Builds (e : SE) : Prop :=
  ∀ (tail : List Tok) (cur : List SE) (stk : List (List SE)),
    build (tokens e ++ tail) (cur :: stk) = build tail ((e :: cur) :: stk)

private def BuildsForms (es : List SE) : Prop :=
  ∀ (tail : List Tok) (cur : List SE) (stk : List (List SE)),
    build (tokensForms es ++ tail) (cur :: stk) = build tail ((es.reverse ++ cur) :: stk)

private theorem builds_atom (s : String) : Builds (.atom s) := by
  intro tail cur stk
  rfl

private theorem builds_list (es : List SE) (ih : BuildsForms es) : Builds (.list es) := by
  intro tail cur stk
  simp only [tokens, List.cons_append, List.append_assoc, build]
  rw [ih]
  simp [build]

private theorem builds_nil : BuildsForms [] := by
  intro tail cur stk
  rfl

private theorem builds_cons (e : SE) (es : List SE) (he : Builds e)
    (hes : BuildsForms es) : BuildsForms (e :: es) := by
  intro tail cur stk
  simp only [tokensForms, List.append_assoc]
  rw [he, hes]
  simp [List.reverse_cons, List.append_assoc]

/-- Expression tokens reconstruct exactly their expression inside any stack. -/
theorem build_tokens (e : SE) (tail : List Tok) (cur : List SE) (stk : List (List SE)) :
    build (tokens e ++ tail) (cur :: stk) = build tail ((e :: cur) :: stk) :=
  SE.rec (motive_1 := Builds) (motive_2 := BuildsForms)
    builds_atom builds_list builds_nil builds_cons e tail cur stk

/-- Form tokens extend the current reversed list in source order. -/
theorem build_tokensForms (es : List SE) (tail : List Tok) (cur : List SE)
    (stk : List (List SE)) :
    build (tokensForms es ++ tail) (cur :: stk) = build tail ((es.reverse ++ cur) :: stk) :=
  SE.rec_1 (motive_1 := Builds) (motive_2 := BuildsForms)
    builds_atom builds_list builds_nil builds_cons es tail cur stk

private def TokensLegal (e : SE) : Prop :=
  LegalExpr e → ∀ t ∈ tokens e, LegalToken t

private def FormsTokensLegal (es : List SE) : Prop :=
  (∀ e ∈ es, LegalExpr e) → ∀ t ∈ tokensForms es, LegalToken t

private theorem legal_atom (s : String) : TokensLegal (.atom s) := by
  intro hs t ht
  cases hs with
  | atom hs =>
    simp only [tokens, List.mem_singleton] at ht
    subst t
    exact hs

private theorem legal_list (es : List SE) (ih : FormsTokensLegal es) :
    TokensLegal (.list es) := by
  intro hs t ht
  cases hs with
  | list hs =>
    simp only [tokens, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl
    · trivial
    · exact ih hs t ht
    · trivial

private theorem legal_nil : FormsTokensLegal [] := by
  intro hs t ht
  simp [tokensForms] at ht

private theorem legal_cons (e : SE) (es : List SE) (he : TokensLegal e)
    (hes : FormsTokensLegal es) : FormsTokensLegal (e :: es) := by
  intro hs t ht
  have hhead : LegalExpr e := hs e (by simp)
  have htail : ∀ a ∈ es, LegalExpr a := fun a ha => hs a (by simp [ha])
  simp only [tokensForms, List.mem_append] at ht
  exact ht.elim (he hhead t) (hes htail t)

theorem tokensForms_legal (es : List SE) (hes : ∀ e ∈ es, LegalExpr e) :
    ∀ t ∈ tokensForms es, LegalToken t :=
  SE.rec_1 (motive_1 := TokensLegal) (motive_2 := FormsTokensLegal)
    legal_atom legal_list legal_nil legal_cons es hes

/-- Actual reader round-trip through both lexical and structural passes. -/
theorem read_renderForms (es : List SE) (hes : ∀ e ∈ es, LegalExpr e) :
    readForms (renderForms es) = some es := by
  have ht : ∀ t ∈ tokensForms es, LegalToken t := tokensForms_legal es hes
  have hl : lex (renderTokens (tokensForms es)) false [] [] = some (tokensForms es) := by
    simpa [lex, flush] using lex_tokens (tokensForms es) ht [] []
  unfold readForms renderForms
  rw [hl]
  change build (tokensForms es) [[]] = some es
  have hb := build_tokensForms es [] [] []
  simpa [build] using hb

theorem read_render (e : SE) (he : LegalExpr e) : readForms (render e) = some [e] := by
  apply read_renderForms
  intro a ha
  have ha' : a = e := List.mem_singleton.mp ha
  exact ha' ▸ he

end Silmaril.Logic.Smt.SExpr.Writer
