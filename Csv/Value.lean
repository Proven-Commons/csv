/-
  The CSV data model and the canonical printer, following
  RFC 4180, with the well formed predicate the round trip proof in
  `Proofs` uses.

  A document is a list of records, a record is a list of fields,
  and a field is text, held as a list of characters. A header row
  is a record like any other at this layer: nothing here maps a
  record to names.

  Any field text is allowed in the model, including commas, quotes,
  carriage returns, and line feeds. The printer quotes a field
  exactly when its text holds one of those characters, and writes
  quotes inside a quoted field twice.
-/

namespace Csv

/-- A field: text, held as a list of characters. -/
abbrev Field := List Char

/-- A record: a list of fields. -/
abbrev Record := List Field

/-- A document: a list of records. -/
abbrev Doc := List Record

/-- The characters that may not sit in an unquoted field, and that
    make the printer quote a field: comma, quote, carriage return,
    line feed. An `abbrev`, so the boolean test below can decide
    it. -/
abbrev IsSpecial (c : Char) : Prop :=
  c = ',' ∨ c = '"' ∨ c = '\r' ∨ c = '\n'

/-- The same test, as a boolean. -/
def isSpecial (c : Char) : Bool := decide (IsSpecial c)

/-- A field is quoted on printing exactly when it holds a comma, a
    quote, a carriage return, or a line feed. -/
def needsQuote (f : Field) : Bool := f.any isSpecial

/-- A field body with every quote written twice, as a quoted field
    holds it. -/
def doubleQuotes : List Char → List Char
  | [] => []
  | c :: cs => (if c = '"' then ['"', '"'] else [c]) ++ doubleQuotes cs

/-- One field in its printed form: quoted, with its quotes doubled,
    when it holds a special character; the text itself otherwise. -/
def printField (f : Field) : List Char :=
  if needsQuote f then '"' :: (doubleQuotes f ++ ['"']) else f

/-- The printed form of the fields after the first in a record: a
    comma before each one. -/
def printFieldsTail : List Field → List Char
  | [] => []
  | f :: fs => ',' :: (printField f ++ printFieldsTail fs)

/-- The fields of one record in printed form, joined by commas. -/
def printFields : List Field → List Char
  | [] => []
  | f :: fs => printField f ++ printFieldsTail fs

/-- One record in printed form: its fields, then CRLF. Every record
    the printer writes ends with CRLF, the last one included. -/
def printRecord (rec : Record) : List Char :=
  printFields rec ++ ['\r', '\n']

/-- A document in printed form: its records in order, each ending
    with CRLF. Zero records print as the empty text. -/
def print (doc : Doc) : List Char :=
  doc.flatMap printRecord

/-- A document is well formed when every record holds at least one
    field. Field texts need no further condition: every list of
    characters prints in a form the parser reads back. -/
def WF (doc : Doc) : Prop :=
  ∀ rec ∈ doc, rec ≠ []

end Csv
