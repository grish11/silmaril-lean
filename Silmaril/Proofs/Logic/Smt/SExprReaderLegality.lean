module

public import Silmaril.Logic.Smt.SExpr.Writer.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.SExpr.Writer

private theorem char_nat {n : Nat} (hn : n < 128) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat, UInt32.toNat]

private theorem flush_legal (cur : List Char) (acc : List Tok)
    (hcur : ∀ c ∈ cur, LegalChar c) (hacc : ∀ t ∈ acc, LegalToken t) :
    ∀ t ∈ flush cur acc, LegalToken t := by
  cases cur with
  | nil => simpa [flush] using hacc
  | cons c cs =>
    intro t ht
    simp only [flush, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at ht
    rcases ht with rfl | ht
    · show LegalAtom (String.ofList (c :: cs).reverse)
      constructor
      · simp
      · intro d hd
        have hd' : d ∈ c :: cs := by simpa [or_comm] using hd
        exact hcur d hd'
    · exact hacc t ht

private theorem token_cons_legal (t : Tok) (ts : List Tok) (ht : LegalToken t)
    (hts : ∀ u ∈ ts, LegalToken u) : ∀ u ∈ t :: ts, LegalToken u := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ht
  · exact hts u hu

/-- The actual lexer preserves legal token buffers even while comments skip
arbitrary bytes. No lexical condition is imposed on the unread bytes. -/
theorem lex_legal (bytes : List UInt8) (comment : Bool) (cur : List Char) (acc ts : List Tok)
    (hcur : ∀ c ∈ cur, LegalChar c) (hacc : ∀ t ∈ acc, LegalToken t)
    (h : lex bytes comment cur acc = some ts) : ∀ t ∈ ts, LegalToken t := by
  induction bytes generalizing comment cur acc ts with
  | nil =>
    have he : (flush cur acc).reverse = ts := Option.some.inj h
    subst ts
    intro t ht
    exact flush_legal cur acc hcur hacc t (List.mem_reverse.mp ht)
  | cons b bytes ih =>
    show ∀ t ∈ ts, LegalToken t
    cases comment with
    | true => exact ih (b.toNat != 10) cur acc ts hcur hacc h
    | false =>
      show ∀ t ∈ ts, LegalToken t
      have hempty : ∀ c ∈ ([] : List Char), LegalChar c := by simp
      have hflush : ∀ t ∈ flush cur acc, LegalToken t := flush_legal cur acc hcur hacc
      have hlp : ∀ t ∈ Tok.lp :: flush cur acc, LegalToken t := token_cons_legal _ _ trivial hflush
      have hrp : ∀ t ∈ Tok.rp :: flush cur acc, LegalToken t := token_cons_legal _ _ trivial hflush
      simp only [lex] at h
      split at h
      · exact ih true [] (flush cur acc) ts hempty hflush h
      · show ∀ t ∈ ts, LegalToken t
        split at h
        · exact ih false [] (.lp :: flush cur acc) ts hempty hlp h
        · show ∀ t ∈ ts, LegalToken t
          split at h
          · exact ih false [] (.rp :: flush cur acc) ts hempty hrp h
          · show ∀ t ∈ ts, LegalToken t
            split at h
            · exact ih false [] (flush cur acc) ts hempty hflush h
            · show ∀ t ∈ ts, LegalToken t
              split at h
              · contradiction
              · show ∀ t ∈ ts, LegalToken t
                simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at *
                have hn : b.toNat < 128 := by omega
                have hlo : 33 ≤ b.toNat := by omega
                have hc : LegalChar (Char.ofNat b.toNat) := by
                  rw [LegalChar, char_nat hn]
                  omega
                have hcur' : ∀ c ∈ Char.ofNat b.toNat :: cur, LegalChar c := by
                  intro c hc'
                  rcases List.mem_cons.mp hc' with rfl | hc'
                  · exact hc
                  · exact hcur c hc'
                exact ih false (Char.ofNat b.toNat :: cur) acc ts hcur' hacc h

private def LegalForms (es : List SE) : Prop := ∀ e ∈ es, LegalExpr e
private def LegalStack (stk : List (List SE)) : Prop := ∀ es ∈ stk, LegalForms es

private theorem stack_cons (es : List SE) (stk : List (List SE))
    (hes : LegalForms es) (hstk : LegalStack stk) : LegalStack (es :: stk) := by
  intro xs hxs
  rcases List.mem_cons.mp hxs with rfl | hxs
  · exact hes
  · exact hstk xs hxs

private theorem forms_cons (e : SE) (es : List SE)
    (he : LegalExpr e) (hes : LegalForms es) : LegalForms (e :: es) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact he
  · exact hes x hx

private theorem forms_reverse (es : List SE) (hes : LegalForms es) : LegalForms es.reverse := by
  intro e he
  exact hes e (List.mem_reverse.mp he)

private theorem build_legal_aux (ts : List Tok) (stk : List (List SE)) (es : List SE)
    (hts : ∀ t ∈ ts, LegalToken t) (hstk : LegalStack stk)
    (h : build ts stk = some es) : LegalForms es := by
  induction ts generalizing stk es with
  | nil =>
    show LegalForms es
    cases stk with
    | nil => simp [build] at h
    | cons top stk =>
      show LegalForms es
      cases stk with
      | nil =>
        have he : top.reverse = es := Option.some.inj h
        subst es
        exact forms_reverse top (hstk top (by simp))
      | cons _ _ => simp [build] at h
  | cons t ts ih =>
    show LegalForms es
    have ht : LegalToken t := hts t (by simp)
    have htail : ∀ u ∈ ts, LegalToken u := fun u hu => hts u (by simp [hu])
    cases t with
    | lp => exact ih ([] :: stk) es htail (stack_cons [] stk (by simp [LegalForms]) hstk) h
    | atom s =>
      show LegalForms es
      cases stk with
      | nil => simp [build] at h
      | cons cur stk =>
        show LegalForms es
        have hcur : LegalForms cur := hstk cur (by simp)
        have hrest : LegalStack stk := fun xs hxs => hstk xs (by simp [hxs])
        exact ih ((.atom s :: cur) :: stk) es htail
          (stack_cons _ _ (forms_cons _ _ (.atom ht) hcur) hrest) h
    | rp =>
      show LegalForms es
      cases stk with
      | nil => simp [build] at h
      | cons cur stk =>
        show LegalForms es
        cases stk with
        | nil => simp [build] at h
        | cons parent stk =>
          have hcur : LegalForms cur := hstk cur (by simp)
          have hparent : LegalForms parent := hstk parent (by simp)
          have hrest : LegalStack stk := fun xs hxs => hstk xs (by simp [hxs])
          exact ih ((.list cur.reverse :: parent) :: stk) es htail
            (stack_cons _ _ (forms_cons _ _ (.list (forms_reverse cur hcur)) hparent) hrest) h

/-- Every form returned by the actual reader has nonempty lexer-safe atoms.
Comments may contain arbitrary bytes; only emitted atoms satisfy the invariant. -/
theorem readForms_legal (bytes : List UInt8) (es : List SE)
    (h : readForms bytes = some es) : ∀ e ∈ es, LegalExpr e := by
  change (lex bytes false [] []).bind _ = some es at h
  obtain ⟨ts, hlex, hbuild⟩ := Option.bind_eq_some_iff.mp h
  have hts : ∀ t ∈ ts, LegalToken t := lex_legal bytes false [] [] ts (by simp) (by simp) hlex
  exact build_legal_aux ts [[]] es hts (by simp [LegalStack, LegalForms]) hbuild

end Silmaril.Logic.Smt.SExpr.Writer
