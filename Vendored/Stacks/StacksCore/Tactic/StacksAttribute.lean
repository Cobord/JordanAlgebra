module

public import Mathlib.Tactic.CrossRefAttribute
public meta import Mathlib.Tactic.CrossRefAttribute
public import StacksCore.Tactic.EgaSgaAttribute

/-! # Utilities for Stacks tags

This module provides the following:
- `@[stacks_fixed TAG]` that fixes `@[stacks]` and works for structures
- `add_to_stacks TAG "comment" DECL` that adds a stacks tag to an upstream declaration
- `#stacks_tags?` that lists the new stacks tags introduced in the current file

-/

@[expose] public section

meta section

open Mathlib.CrossRef Lean Elab Parser Meta System Command

/-- The syntax for a "stacks" database identifier in a `@[stacks_fixed]` attribute. -/
syntax (name := stacksTag') "stacks_fixed" stacksTagParser (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `stacksTag'
  descr := "Apply a Stacks or Kerodon project tag to a theorem."
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let (SorK, database, url, tag, comment) ← match stx with
      | `(attr| stacks_fixed $tag $[$comment]?) =>
        pure ("stacks", Database.stacks, "https://stacks.math.columbia.edu/tag", tag, comment)
      | _ => throwUnsupportedSyntax
    let tagStr ← tag.getStacksTag
    let comment := (comment.map (·.getString)).getD ""
    let commentInDoc := if comment = "" then "" else s!" ({comment})"
    let newDoc := [oldDoc, s!"[{SorK} Tag {tagStr}]({url}/{tagStr}){commentInDoc}"]
    addDocStringCore decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addTagEntry decl database tagStr <| comment
  -- The key to making this fire for `structure`
  applicationTime := .afterTypeChecking
}

/-- Add a stacks tag to an upstream declaration. Usage:

`add_to_stacks F05F "lorem ipsum" CategoryTheory.foo` -/
syntax (name := addToStacks)
  "add_to_stacks " stacksTagParser (ppSpace str)? ppSpace ident : command

/-- Elaborator for the `add_to_stacks` command -/
@[command_elab addToStacks]
def addToStacksElab : CommandElab := fun stx ↦ match stx with
  | `(command| add_to_stacks $tag $[$comment]? $declStx:ident) => do
    let tagStr ← liftCoreM tag.getStacksTag
    let comment := (comment.map (·.getString)).getD ""
    let declList ← resolveGlobalConst declStx
    let [decl] := declList | throwError m!"Ambiguous identifier: {declList}"
    runTermElabM fun _ ↦ do Term.addTermInfo' declStx (← mkConst' decl)
    -- Warn if this declaration already carries this Stacks tag, so that
    -- `add_to_stacks` cannot silently record the same tag twice.
    let state := PersistentEnvExtension.getState tagExt (← getEnv)
    let existing := state.2.flatten.toList ++ state.1
    if existing.any fun t => t.declName == decl && t.database == .stacks && t.tag == tagStr then
      logWarningAt stx
        m!"'{decl}' already has the stacks tag {tagStr}; skipping duplicate."
    addTagEntry decl .stacks tagStr comment
  | _ => throwUnsupportedSyntax

/-- Check new stacks tags due to this file -/
elab "#stacks_tags?" : command => do
  let data := PersistentEnvExtension.getState tagExt (← getEnv)
  let mut debug : MessageData := ""
  for tag in data.1 do
    have db := tag.database.label
    have cmt := if tag.comment = "" then "" else s!" ({tag.comment})"
    let term ← liftCoreM (mkConst' tag.declName).run
    debug := debug ++ m!"{db} {tag.tag}{cmt}: {term.1}\n"
  logInfo debug
