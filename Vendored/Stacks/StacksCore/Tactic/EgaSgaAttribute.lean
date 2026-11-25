module

public meta import Lean

/-! # EGA and SGA cross-references

Grothendieck's *Éléments de géométrie algébrique* (EGA, with Dieudonné) and the
*Séminaire de géométrie algébrique* (SGA) are cited by volume and printed number.
This module records such citations on declarations, next to `@[stacks]` tags:

- `@[ega "IV 5.8.6"]`, `@[ega "0 23.1.1" "(i)"]`: EGA volume (`0`, `I`, `II`, `III`,
  `IV`) and the printed number, whose first component is the section.
- `@[sga "4 IV 4.9.4"]`, `@[sga "1 I 9.5" "(ii)"]`: SGA volume (`1`, `2`, `3`, `4`, `4½`,
  `5`, `6`, `7`), exposé, and the printed number within the exposé.
- `add_to_ega "IV 5.8.6" "(ii)" decl` and `add_to_sga ...` attach a reference to a
  declaration defined elsewhere (for example in Mathlib).
- `#ega_sga_tags?` lists the references introduced in the current file.

The optional comment says which part of the printed item the declaration realizes, as a
short marker such as a clause `"(ii)"`, `"a) ⇒ c)"`, `"converse"` or `"affine case"`, at
most `maxCommentLength` characters. It names what is proved, not what is left out. A
reference with no comment claims the whole printed item.

Numbers follow the original installments (Publ. Math. IHÉS for EGA; the standard
Springer LNM editions for SGA).

The environment extension `refExt` is the record of which declaration realizes which
reference; tools read it (as `GetStacksPairs` reads Mathlib's `tagExt`). A declaration
without its own docstring also gets a readable line such as `EGA IV₂, §5, (5.8.6)`, naming
the installment in which the section is printed. As with Mathlib's `@[stacks]`, a
docstring written on the declaration itself is attached after the attribute runs, so
that line does not appear there.
-/

@[expose] public section

meta section

open Lean Elab Command

namespace Stacks.EgaSga

/-- The two collections. -/
inductive Work where
  | ega
  | sga
  deriving BEq, Hashable, Inhabited, Repr

/-- A recorded reference: `ref` is the validated reference string, e.g. `"IV 5.8.6"`. -/
structure Ref where
  /-- The declaration carrying the reference. -/
  declName : Name
  /-- EGA or SGA. -/
  work : Work
  /-- The validated reference, e.g. `"IV 5.8.6"` or `"4 IV 4.9.4"`. -/
  ref : String
  /-- What the declaration covers when it is not the whole item, e.g. `"(ii)"`. -/
  comment : String
  deriving BEq, Hashable, Inhabited, Repr

/-- The environment extension recording every EGA/SGA reference. -/
initialize refExt : SimplePersistentEnvExtension Ref (Array (Array Ref)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun refs => refs
    addEntryFn := fun refs _ => refs
  }

/-- Every reference visible in `env`, imported ones included. -/
def allRefs (env : Environment) : Array Ref :=
  let state := PersistentEnvExtension.getState refExt env
  state.2.flatten ++ state.1.toArray.reverse

/-- A printed number: positive integers separated by dots, e.g. `5.8.6` or `23.1.1.2`. -/
def isNumber (s : String) : Bool :=
  let parts := s.splitOn "."
  parts.length ≥ 2 && parts.all fun p => !p.isEmpty && p.all Char.isDigit

/-- The installment of EGA in which section `sec` of volume `vol` is printed.  EGA IV₁
(Publ. Math. IHÉS 20) holds Chapter 0, §§14–23, and Chapter IV, §1 only; IV₂ starts at §2. -/
def egaPart (vol : String) (sec : Nat) : Option String :=
  match vol with
  | "0" =>
    if sec ≤ 7 then some "0_I (in EGA I)"
    else if sec ≤ 13 then some "0_III (in EGA III₁)"
    else if sec ≤ 23 then some "0_IV (in EGA IV₁)" else none
  | "I" => if 1 ≤ sec ∧ sec ≤ 10 then some "I" else none
  | "II" => if 1 ≤ sec ∧ sec ≤ 8 then some "II" else none
  | "III" =>
    if 1 ≤ sec ∧ sec ≤ 5 then some "III₁"
    else if sec ≤ 7 then some "III₂" else none
  | "IV" =>
    if sec = 1 then some "IV₁"
    else if 2 ≤ sec ∧ sec ≤ 7 then some "IV₂"
    else if sec ≤ 15 then some "IV₃"
    else if sec ≤ 21 then some "IV₄" else none
  | _ => none

/-- Validate an EGA reference `"VOL NUMBER"` and render it for the docstring. -/
def parseEga (ref : String) : Except String String := do
  let [vol, num] := (ref.splitOn " ").filter (· ≠ "") |
    throw s!"expected \"VOLUME NUMBER\", e.g. \"IV 5.8.6\", got \"{ref}\""
  unless isNumber num do throw s!"\"{num}\" is not a printed number such as 5.8.6"
  let sec := ((num.splitOn ".").headD "0").toNat!
  let some part := egaPart vol sec |
    throw s!"EGA {vol} has no section {sec} (volumes: 0, I, II, III, IV)"
  return s!"EGA {part}, §{sec}, ({num})"

/-- SGA volumes. -/
def sgaVolumes : List String := ["1", "2", "3", "4", "4½", "5", "6", "7"]

/-- An exposé: a Roman numeral, possibly with a suffix as in `Vbis` or `VIIB`, or `0`
(the introductory exposé of SGA 6). -/
def isExposé (s : String) : Bool :=
  s == "0" || (s.front ∈ ['I', 'V', 'X'] && s.all Char.isAlpha)

/-- An SGA number: dot-separated components of letters and digits, since some items are
numbered inside appendices (`App.1.1`) or by clause (`1.1(a)`). -/
def isSgaNumber (s : String) : Bool :=
  let parts := s.splitOn "."
  let allowed (c : Char) : Bool := c.isAlphanum || c == '(' || c == ')'
  parts.all (fun p => !p.isEmpty && p.all allowed) && s.any Char.isDigit

/-- Validate an SGA reference `"VOL EXPOSÉ NUMBER"` and render it for the docstring.
SGA 4½ has named parts instead of numbered exposés; they are written as one word with
underscores for spaces (`Th_finitude`). -/
def parseSga (ref : String) : Except String String := do
  let [vol, exp, num] := (ref.splitOn " ").filter (· ≠ "") |
    throw s!"expected \"VOLUME EXPOSÉ NUMBER\", e.g. \"4 IV 4.9.4\", got \"{ref}\""
  unless vol ∈ sgaVolumes do throw s!"SGA has no volume {vol} (volumes: {sgaVolumes})"
  unless vol == "4½" || isExposé exp do throw s!"\"{exp}\" is not an exposé numeral"
  unless isSgaNumber num do throw s!"\"{num}\" is not a printed number such as 4.9.4"
  let exposé := if vol == "4½" then exp.replace "_" " " else s!"Exp. {exp}"
  return s!"SGA {vol}, {exposé}, ({num})"

/-- A comment as it appears after a reference: clauses such as `(ii)` keep their own
parentheses, anything else is parenthesized. -/
def commentSuffix (comment : String) : String :=
  if comment.isEmpty then "" else if comment.startsWith "(" then s!" {comment}" else
    s!" ({comment})"

/-- The longest comment accepted: a clause marker, not an explanation. -/
def maxCommentLength : Nat := 24

/-- Validate and record the reference, appending a docstring line when the docstring can
still be changed (not for imported declarations, nor after elaboration has moved on). -/
def addRef (decl : Name) (work : Work) (ref comment : String) : CoreM Unit := do
  let ref := " ".intercalate ((ref.splitOn " ").filter (· ≠ ""))
  let rendered ← match (match work with | .ega => parseEga ref | .sga => parseSga ref) with
    | .ok r => pure r
    | .error e => throwError e
  if comment.length > maxCommentLength then
    throwError m!"the comment \"{comment}\" is {comment.length} characters; name the clause \
      realized in at most {maxCommentLength}, e.g. \"(ii)\" or \"affine case\""
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  try
    addDocStringCore decl <|
      "\n\n".intercalate ([oldDoc, rendered ++ commentSuffix comment].filter (· != ""))
  catch _ => pure ()
  let env ← getEnv
  if (allRefs env).any fun r => r.declName == decl && r.work == work && r.ref == ref then
    logWarning m!"'{decl}' already carries this reference; skipping duplicate."
  else
    modifyEnv (refExt.addEntry · { declName := decl, work, ref, comment })

/-- `@[ega "IV 5.8.6" "(ii)"]`: the declaration realizes EGA IV (5.8.6). -/
syntax (name := egaAttr) "ega " str (ppSpace str)? : attr
/-- `@[sga "4 IV 4.9.4" "(ii)"]`: the declaration realizes SGA 4, Exp. IV (4.9.4). -/
syntax (name := sgaAttr) "sga " str (ppSpace str)? : attr

initialize
  for (name, work) in [(`egaAttr, Work.ega), (`sgaAttr, Work.sga)] do
    registerBuiltinAttribute {
      name
      descr := "Record an EGA or SGA reference realized by this declaration."
      add := fun decl stx _ => do
        let (ref, comment) ← match stx with
          | `(attr| ega $r $[$c]?) | `(attr| sga $r $[$c]?) =>
            pure (r.getString, (c.map (·.getString)).getD "")
          | _ => throwUnsupportedSyntax
        addRef decl work ref comment
      -- As for Mathlib's `@[stacks]`: docstrings are immutable once asynchronous
      -- elaboration has started.
      applicationTime := .beforeElaboration
    }

/-- `add_to_ega "IV 5.8.6" "(ii)" decl` records an EGA reference on `decl`. -/
syntax (name := addToEga) "add_to_ega " str (ppSpace str)? ppSpace ident : command
/-- `add_to_sga "4 IV 4.9.4" "(ii)" decl` records an SGA reference on `decl`. -/
syntax (name := addToSga) "add_to_sga " str (ppSpace str)? ppSpace ident : command

/-- Elaborator for `add_to_ega` and `add_to_sga`. -/
@[command_elab addToEga, command_elab addToSga]
def addToElab : CommandElab := fun stx => do
  let (work, ref, comment, declStx) ← match stx with
    | `(command| add_to_ega $r $[$c]? $d:ident) => pure (Work.ega, r, c, d)
    | `(command| add_to_sga $r $[$c]? $d:ident) => pure (Work.sga, r, c, d)
    | _ => throwUnsupportedSyntax
  let [decl] ← liftCoreM (realizeGlobalConstWithInfos declStx) |
    throwError m!"ambiguous identifier {declStx}"
  liftCoreM <| addRef decl work ref.getString ((comment.map (·.getString)).getD "")

/-- List the EGA/SGA references added in the current file. -/
elab "#ega_sga_tags?" : command => do
  let refs := (PersistentEnvExtension.getState refExt (← getEnv)).1.reverse
  let lines := refs.map fun r =>
    let w := match r.work with | .ega => "EGA" | .sga => "SGA"
    m!"{w} {r.ref}{commentSuffix r.comment}: {r.declName}"
  logInfo (MessageData.joinSep lines "\n")

end Stacks.EgaSga
