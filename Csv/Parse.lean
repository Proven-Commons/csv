/-
  The CSV parser. It reads a list of characters and returns a
  document, or `none` when the text sits outside the grammar the
  plan states, which follows RFC 4180 with CRLF as the only record
  separator on reading.

  Rules the parser follows:

  - Records are split by CRLF. The last record may end without a
    CRLF. Empty input reads as zero records, and a trailing CRLF
    after the last record does not add a record.
  - An unquoted field holds any run of characters except comma,
    quote, CR, and LF, and ends at a comma, a CRLF, or the end of
    the input.
  - A quoted field starts with a quote at the start of a field.
    Inside it any character may appear; a quote written twice
    reads as one quote. The closing quote must be followed by a
    comma, a CRLF, or the end of the input.
  - A bare CR not followed by LF, a bare LF, a quote in the middle
    of an unquoted field, characters after a closing quote other
    than the three followers, and a quoted field that never closes
    are all rejected.
  - Spaces are field data. Nothing is trimmed.

  `parseFields` and `parseDoc` take a fuel count: each field of a
  record spends one unit in `parseFields`, and each record spends
  one unit in `parseDoc`. The top level `parse` passes one more
  than the length of the text to `parseDoc`, and `parseDoc` passes
  one more than the length of its remaining text to `parseFields`.
  Both are always enough for a text the grammar accepts, and a
  hostile text is rejected, never looped on.
-/

import Csv.Value

namespace Csv

/-- The longest run of characters that may sit in an unquoted
    field, and the text after the run. The run stops at a comma, a
    quote, a CR, an LF, or the end of the text. -/
def takePlain : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isSpecial c then ([], c :: cs)
    else
      let (f, r) := takePlain cs
      (c :: f, r)

/-- Read a quoted field body. The input starts just after the
    opening quote. A quote followed by a quote reads as one quote;
    a quote followed by anything else closes the field. Returns
    the field and the text after the closing quote, or `none` when
    the text ends before the field closes. -/
def parseQuoted : List Char → Option (Field × List Char)
  | [] => none
  | '"' :: '"' :: rest => (parseQuoted rest).map fun (f, r) => ('"' :: f, r)
  | '"' :: rest => some ([], rest)
  | c :: rest => (parseQuoted rest).map fun (f, r) => (c :: f, r)

/-- Read one field from the front of the text. A quote at the
    start of a field opens a quoted field; anything else starts a
    plain field. Returns the field and the text after it. That
    text is empty, or starts with a comma, or starts with a CRLF;
    when the text after the field is none of those, the result is
    `none`. Callers check the follower. -/
def parseField : List Char → Option (Field × List Char)
  | [] => some ([], [])
  | c :: rest =>
    if c = '"' then parseQuoted rest
    else
      let (f, r) := takePlain (c :: rest)
      match r with
      | [] => some (f, [])
      | ',' :: _ => some (f, r)
      | '\r' :: '\n' :: _ => some (f, r)
      | _ => none

/-- Read the fields of one record from the front of the text.
    Returns the fields and the text after the record: what follows
    the CRLF that ends it, or empty when the end of the text ends
    the record. -/
def parseFields : Nat → List Char → Option (Record × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match parseField cs with
    | none => none
    | some (f, r) =>
      match r with
      | [] => some ([f], [])
      | ',' :: r' =>
        match parseFields fuel r' with
        | none => none
        | some (fs, r'') => some (f :: fs, r'')
      | '\r' :: '\n' :: r' => some ([f], r')
      | _ => none

/-- Read the records of a document from the front of the text.
    Empty text reads as zero records. -/
def parseDoc : Nat → List Char → Option Doc
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, cs =>
    match parseFields (cs.length + 1) cs with
    | none => none
    | some (rec, r) =>
      match parseDoc fuel r with
      | none => none
      | some ds => some (rec :: ds)

/-- Parse a whole text as a document. -/
def parse (cs : List Char) : Option Doc :=
  parseDoc (cs.length + 1) cs

end Csv
