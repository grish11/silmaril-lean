module

public import Silmaril.Courses.Cambridge.Concrete.Lexer

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concrete

/-- A token that has a spelling in the base L1/L2 vocabulary. -/
def Token.Spellable : Token → Prop
  | .keyword (.data _) => False
  | .location s => IsLocation s
  | .variable s => IsVariable s
  | _ => True

private theorem word_not_whitespace {c : Char} (h : wordChar c = true) :
    whitespace c = false := by
  cases hw : whitespace c
  · rfl
  · simp [whitespace, Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with ((rfl | rfl) | rfl) | rfl <;> contradiction

private theorem takeDrop_word {cs : List Char} (h : cs.all wordChar = true) :
    cs.takeWhile wordChar = cs ∧ cs.dropWhile wordChar = [] := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.takeWhile, List.dropWhile, h.1, (ih h.2).1, (ih h.2).2]

private theorem scan_word {cs : List Char} (h : IsWord cs) :
    scan cs.length cs = (classifyWord cs).map List.singleton := by
  rcases cs with _ | ⟨c, cs⟩
  · exact (h.1 rfl).elim
  · have hc := h.2
    simp only [List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨htake, hdrop⟩ := takeDrop_word hc.2
    simp [scan, hc.1, htake, hdrop]
    cases classifyWord (c :: cs) <;> rfl

private theorem spell_word {token : Token} {cs : List Char} (hword : IsWord cs)
    (hclass : classifyWord cs = some token) :
    (∀ c ∈ cs, whitespace c = false) ∧ scan cs.length cs = some [token] :=
  ⟨fun c hc => word_not_whitespace (List.all_eq_true.mp hword.2 c hc),
    by rw [scan_word hword, hclass]; rfl⟩

private theorem spell_token {token : Token} (h : token.Spellable) :
    (∀ c ∈ token.chars, whitespace c = false) ∧
      scan token.chars.length token.chars = some [token] := by
  cases token with
  | keyword k =>
    refine ⟨fun c hc => ?_, ?_⟩
    · have hs := show (Token.keyword k).chars.all (fun c => !whitespace c) = true by
        cases k <;> first | exact h.elim | decide
      simpa using List.all_eq_true.mp hs c hc
    · cases k <;> first | exact h.elim | decide
  | punct p =>
    refine ⟨fun c hc => ?_, ?_⟩
    · have h := show (Token.punct p).chars.all (fun c => !whitespace c) = true by
        cases p <;> decide
      simpa using List.all_eq_true.mp h c hc
    · cases p <;> decide
  | location s => exact spell_word h.1 h.2
  | «variable» s => exact spell_word h.1 h.2
  | number n =>
    have hd : ∀ c ∈ n.repr.toList, c.isDigit = true := by
      intro c hc
      exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) (Nat.toList_repr ▸ hc)
    apply spell_word
    · refine ⟨?_, List.all_eq_true.mpr ?_⟩
      · simpa only [Token.chars, Nat.toList_repr] using (Nat.toDigits_ne_nil (n := n) (b := 10))
      · exact fun c hc => by simp [wordChar, Char.isAlphanum, hd c hc]
    · change classifyWord n.repr.toList = some (.number n)
      rw [classifyWord, ite_eq_left (List.all_eq_true.mpr hd), String.ofList_toList, Nat.toNat?_repr]
      rfl

private theorem scan_renderChars (tokens : List Token)
    (h : ∀ t ∈ tokens, Token.Spellable t) :
    scanChunks ((renderChars tokens).splitOnP whitespace) = some tokens := by
  induction tokens with
  | nil => simp [renderChars, scanChunks, scan]
  | cons t ts ih =>
    obtain ⟨hspace, hscan⟩ := spell_token (h t (by simp))
    cases ts with
    | nil =>
      rw [renderChars, List.splitOnP_eq_singleton hspace]
      simp [scanChunks, hscan]
    | cons next rest =>
      rw [renderChars, List.splitOnP_append_cons_of_forall_mem hspace ' ' (by decide)]
      simp [scanChunks, hscan, ih (fun token hm => h token (List.mem_cons_of_mem _ hm))]

/-- Canonical UTF-8 rendering is a section of the tokenizer on source tokens. -/
theorem tokenize_render (tokens : List Token) (h : ∀ t ∈ tokens, Token.Spellable t) :
    tokenize (render tokens) = some tokens := by
  unfold tokenize render String.fromUTF8?
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    ByteArray.isValidUTF8_utf8Encode, dite_true, String.fromUTF8_eq_ofByteArray]
  change scanChunks ((String.ofList (renderChars tokens)).toList.splitOnP whitespace) = _
  simpa only [String.toList_ofList] using scan_renderChars tokens h

end Silmaril.Courses.Cambridge.Concrete
