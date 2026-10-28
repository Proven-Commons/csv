/-
  The round trip proof: for every well formed document, parsing
  its printed form gives the document back.

  The statement proved here is `parse_print`. A matching statement
  in a spec file still has to be added by a reviewer, so this file
  builds on its own, in the same shape as the json proofs.

  The steps mirror the json string work, with quote doubling in
  place of backslash escapes: a plain field is read back by the
  plain run reader, a quoted field by the quoted body reader over
  the doubled quotes, one record at a time, then one document.
-/

import Csv

namespace Csv.Proofs

open Csv

set_option maxRecDepth 10000

/-- The boolean test and the proposition agree. -/
theorem isSpecial_true {c : Char} : isSpecial c = true ↔ IsSpecial c :=
  decide_eq_true_iff

/-- The boolean test and the proposition agree, on the false
    side. -/
theorem isSpecial_false {c : Char} : isSpecial c = false ↔ ¬ IsSpecial c :=
  decide_eq_false_iff_not

/-- Reading a plain run off the front of a text: when every
    character of `l` is plain and what follows is empty or starts
    with a special character, the run is exactly `l`. -/
theorem takePlain_append {l r : List Char}
    (hl : ∀ c ∈ l, isSpecial c = false)
    (hr : r = [] ∨ ∃ c cs, r = c :: cs ∧ isSpecial c = true) :
    takePlain (l ++ r) = (l, r) := by
  induction l with
  | nil =>
    cases hr with
    | inl h => simp [h, takePlain]
    | inr h =>
      obtain ⟨c, cs, rfl, hc⟩ := h
      simp [takePlain, hc]
  | cons c cs ih =>
    have hc : isSpecial c = false := hl c (by simp)
    have hcs : ∀ x ∈ cs, isSpecial x = false :=
      fun x hx => hl x (List.mem_cons_of_mem c hx)
    simp [takePlain, hc, ih hcs]

/-- Reading back a quoted body: the doubled quotes of a printed
    field, then its closing quote, read as the field itself. What
    follows the closing quote is empty or starts with a character
    other than a quote, as a separator or the end of the text
    always does. -/
theorem parseQuoted_doubleQuotes : ∀ (f : List Char) (r : List Char),
    (r = [] ∨ ∃ c cs, r = c :: cs ∧ c ≠ '"') →
    parseQuoted (doubleQuotes f ++ '"' :: r) = some (f, r) := by
  intro f
  induction f with
  | nil =>
    intro r hr
    cases hr with
    | inl h => simp [h, doubleQuotes, parseQuoted]
    | inr h =>
      obtain ⟨c, cs, rfl, hc⟩ := h
      simp [doubleQuotes, parseQuoted, hc]
  | cons c cs ih =>
    intro r hr
    by_cases hc : c = '"'
    · subst hc
      have h1 : doubleQuotes ('"' :: cs) = '"' :: '"' :: doubleQuotes cs := by
        simp [doubleQuotes]
      rw [h1]
      show parseQuoted (('"'
        :: ('"' :: doubleQuotes cs)) ++ '"' :: r) = _
      rw [List.cons_append, List.cons_append]
      simp [parseQuoted, ih r hr]
    · have h1 : doubleQuotes (c :: cs) = c :: doubleQuotes cs := by
        simp [doubleQuotes, hc]
      rw [h1]
      show parseQuoted (c :: (doubleQuotes cs ++ '"' :: r)) = _
      simp [parseQuoted, hc, ih r hr]

/-- Reading back one printed field: followed by nothing, by a
    comma, or by a CRLF, the reader returns the field and the
    follower untouched. -/
theorem parseField_printField (f : Field) (r : List Char)
    (hr : r = [] ∨ (∃ t, r = ',' :: t) ∨ (∃ t, r = '\r' :: '\n' :: t)) :
    parseField (printField f ++ r) = some (f, r) := by
  by_cases hq : needsQuote f
  · have hprint : printField f = '"' :: (doubleQuotes f ++ ['"']) := if_pos hq
    rw [hprint]
    simp only [List.cons_append, List.append_assoc]
    show parseField ('"' :: (doubleQuotes f ++ '"' :: r)) = some (f, r)
    rw [show parseField ('"' :: (doubleQuotes f ++ '"' :: r))
          = parseQuoted (doubleQuotes f ++ '"' :: r) from rfl]
    apply parseQuoted_doubleQuotes
    rcases hr with h | ⟨t, h⟩ | ⟨t, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨',', t, h, by decide⟩
    · exact Or.inr ⟨'\r', '\n' :: t, h, by decide⟩
  · have hprint : printField f = f := if_neg hq
    rw [hprint]
    have hplain : ∀ c ∈ f, isSpecial c = false := by
      have h := hq
      simp [needsQuote] at h
      exact h
    have hr' : r = [] ∨ ∃ x xs, r = x :: xs ∧ isSpecial x = true := by
      rcases hr with h | ⟨t, h⟩ | ⟨t, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨',', t, h, by decide⟩
      · exact Or.inr ⟨'\r', '\n' :: t, h, by decide⟩
    have htake : takePlain (f ++ r) = (f, r) := takePlain_append hplain hr'
    cases f with
    | nil =>
      show parseField r = some ([], r)
      rcases hr with h | ⟨t, h⟩ | ⟨t, h⟩
      · subst h; rfl
      · subst h; rfl
      · subst h; rfl
    | cons c cs =>
      have hc : c ≠ '"' := by
        have hcc := hplain c (by simp)
        intro h
        rw [h] at hcc
        simp [isSpecial] at hcc
      rw [List.cons_append]
      have htake2 : takePlain (c :: (cs ++ r)) = (c :: cs, r) := htake
      simp only [parseField, hc]
      rw [htake2]
      rcases hr with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h] <;> rfl

/-- One step of the record reader, stated for rewriting. -/
theorem parseFields_succ (n : Nat) (cs : List Char) :
    parseFields (n + 1) cs =
      match parseField cs with
      | none => none
      | some (f, r) =>
        match r with
        | [] => some ([f], [])
        | ',' :: r' =>
          match parseFields n r' with
          | none => none
          | some (fs, r'') => some (f :: fs, r'')
        | '\r' :: '\n' :: r' => some ([f], r')
        | _ => none := rfl

/-- Reading back one printed record: followed by more text, the
    record reader returns the record and the text after its
    CRLF. -/
theorem parseFields_printFields : ∀ (fs : Record) (m : Nat)
    (r : List Char), fs ≠ [] → fs.length ≤ m →
    parseFields m (printFields fs ++ '\r' :: '\n' :: r) = some (fs, r) := by
  intro fs
  induction fs with
  | nil => intro m r h; simp at h
  | cons f fs ih =>
    intro m r hne hlen
    cases m with
    | zero => simp at hlen
    | succ m =>
      have hR : (printFieldsTail fs ++ '\r' :: '\n' :: r) = []
          ∨ (∃ t, printFieldsTail fs ++ '\r' :: '\n' :: r = ',' :: t)
          ∨ (∃ t, printFieldsTail fs ++ '\r' :: '\n' :: r
              = '\r' :: '\n' :: t) := by
        cases fs with
        | nil =>
          exact Or.inr (Or.inr ⟨r, by simp [printFieldsTail]⟩)
        | cons f' fs' =>
          exact Or.inr (Or.inl ⟨printFields (f' :: fs') ++ '\r' :: '\n' :: r, by
            simp [printFieldsTail, printFields, List.append_assoc]⟩)
      have hpf := parseField_printField f
        (printFieldsTail fs ++ '\r' :: '\n' :: r) hR
      rw [show printFields (f :: fs) = printField f ++ printFieldsTail fs
        from rfl, List.append_assoc, parseFields_succ, hpf]
      cases fs with
      | nil => simp [printFieldsTail]
      | cons f' fs' =>
        have hlen' : (f' :: fs').length ≤ m := by
          simp only [List.length_cons] at hlen ⊢
          omega
        have hI := ih m r (by simp) hlen'
        show (match parseFields m (printFields (f' :: fs') ++ '\r' :: '\n' :: r)
            with
            | none => none
            | some (fs, r'') => some (f :: fs, r'')) = some (f :: f' :: fs', r)
        simp only [hI]

/-- The tail printer writes at least one character per field it
    covers: the comma. -/
theorem printFieldsTail_length : ∀ (fs : Record),
    fs.length ≤ (printFieldsTail fs).length := by
  intro fs
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [printFieldsTail, List.length_cons, List.length_append]
    omega

/-- A printed record is longer than its field count: each field
    after the first adds a comma, and the CRLF adds two. -/
theorem printRecord_length (rec : Record) :
    rec.length + 1 ≤ (printRecord rec).length := by
  cases rec with
  | nil => simp [printRecord, printFields]
  | cons f fs =>
    have h := printFieldsTail_length fs
    simp only [printRecord, printFields, List.length_append,
      List.length_cons]
    omega

/-- A printed document is at least as long as its record count. -/
theorem print_length (doc : Doc) : doc.length ≤ (print doc).length := by
  induction doc with
  | nil => simp [print]
  | cons rec doc ih =>
    have hrec := printRecord_length rec
    have ih' : doc.length ≤ (doc.flatMap printRecord).length := ih
    simp only [print, List.flatMap_cons, List.length_append,
      List.length_cons]
    omega

/-- One step of the document reader, stated for rewriting. -/
theorem parseDoc_succ (n : Nat) (c : Char) (cs : List Char) :
    parseDoc (n + 1) (c :: cs) =
      match parseFields ((c :: cs).length + 1) (c :: cs) with
      | none => none
      | some (rec, r) =>
        match parseDoc n r with
        | none => none
        | some ds => some (rec :: ds) := rfl

/-- Reading back a printed document, at any fuel that covers its
    record count. -/
theorem parseDoc_print : ∀ (doc : Doc) (n : Nat),
    WF doc → doc.length ≤ n → parseDoc n (print doc) = some doc := by
  intro doc
  induction doc with
  | nil => intro n _ _; simp [print, parseDoc]
  | cons rec doc ih =>
    intro n hwf hlen
    have hrec : rec ≠ [] := hwf rec (by simp)
    have hwf' : WF doc := fun r hr => hwf r (List.mem_cons_of_mem rec hr)
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hlenrec : rec.length ≤ (print (rec :: doc)).length + 1 := by
        have h1 := printRecord_length rec
        have h2 : (print (rec :: doc)).length
            = (printRecord rec).length + (print doc).length := by
          simp [print, List.length_append]
        omega
      have hFields := parseFields_printFields rec
        ((print (rec :: doc)).length + 1) (print doc) hrec hlenrec
      have hform : printFields rec ++ '\r' :: '\n' :: print doc
          = print (rec :: doc) := by
        simp [print, printRecord, List.append_assoc]
      have hlen' : doc.length ≤ n := by
        have h3 : (rec :: doc).length = doc.length + 1 := rfl
        omega
      have hI := ih n hwf' hlen'
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, print (rec :: doc) = c :: cs := by
        cases h : print (rec :: doc) with
        | nil =>
          exfalso
          have h2a : (printRecord rec).length
              = (printFields rec).length + 2 := by
            simp [printRecord, List.length_append]
          have h2b : (print (rec :: doc)).length
              = (printRecord rec).length + (print doc).length := by
            simp [print, List.length_append]
          rw [h] at h2b
          simp at h2b
          omega
        | cons c cs => exact ⟨c, cs, rfl⟩
      rw [hcs, parseDoc_succ]
      have hf2 : parseFields ((c :: cs).length + 1) (c :: cs)
          = some (rec, print doc) := by
        have e2 : (c :: cs).length = (print (rec :: doc)).length := by
          rw [hcs]
        have e1 : (c :: cs)
            = printFields rec ++ '\r' :: '\n' :: print doc :=
          hcs.symm.trans hform.symm
        rw [e2, e1]
        exact hFields
      rw [hf2]
      simp only [hI]

/-- The round trip: parsing the printed form of a well formed
    document gives the document back. A document is well formed
    when every record holds at least one field; field texts need
    no further condition. -/
theorem parse_print {doc : Doc} (h : WF doc) : parse (print doc) = some doc :=
  parseDoc_print doc _ h (by
    have h1 := print_length doc
    omega)

end Csv.Proofs
