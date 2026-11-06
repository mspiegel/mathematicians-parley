import Mathlib
import Mathlib.Tactic.MinImports

/-!
# The modules a Parley build's Lean names come from

`parley build lean` asks, for each constant and each piece of syntax its
files write, which modules declare it, so that a file imports those and
not the whole of Mathlib. It caches the answers against the Mathlib
revision, and runs this only for keys the cache lacks:

    lake env lean --run scripts/ModulesOf.lean <asked> <answers>

Each line of `<asked>` is a JSON object with a `kind` and a `key`:

* `const` and a constant's full name;
* `term` or `tactic` and a sample of syntax, parsed in that category: the
  modules of its syntax kinds and of the constants it names.

Each line of `<answers>` is the same object with the `modules` found, or
with an `error` where a sample does not parse. Lean's own `Init` and
`Lean` modules, which every file has, are left out.
-/

open Lean Mathlib.Command.MinImports

/-- Whether a module comes with Lean itself, so that no file imports it. -/
def builtIn (m : Name) : Bool :=
  isInitImport m || (`Lean).isPrefixOf m

/-- The module declaring `n`, where it is a declaration of an imported one. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- The modules declaring the names, Lean's own left out, in order. -/
def modulesOf (env : Environment) (names : NameSet) : Array Name :=
  let found := names.toArray.filterMap (moduleOf env)
  let kept := found.filter (!builtIn ·)
  (kept.foldl (fun (s : NameSet) m => s.insert m) {}).toArray.qsort Name.lt

/-- The modules a key names, or why it names none. -/
def modulesFor (env : Environment) (kind key : String) : Except String (Array Name) :=
  if kind == "const" then
    .ok (modulesOf env (({} : NameSet).insert key.toName))
  else
    match Parser.runParserCategory env kind.toName key with
    | .ok stx => .ok (modulesOf env (getSyntaxNodeKinds stx))
    | .error e => .error e

/-- The answer line for one asked line. -/
def answer (env : Environment) (line : String) : String := Id.run do
  let asked : Except String (String × String) := do
    let j ← Json.parse line
    return (← j.getObjValAs? String "kind", ← j.getObjValAs? String "key")
  match asked with
  | .error e => return (Json.mkObj [("line", line), ("error", e)]).compress
  | .ok (kind, key) =>
    let found := match modulesFor env kind key with
      | .ok ms => ("modules", toJson (ms.map toString))
      | .error e => ("error", toJson e)
    return (Json.mkObj [("kind", kind), ("key", key), found]).compress

unsafe def main (args : List String) : IO UInt32 := do
  let [asked, answers] := args
    | IO.eprintln "usage: ModulesOf <asked> <answers>"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Mathlib }] {} (loadExts := true)
  let lines := (← IO.FS.lines asked).filter (· ≠ "")
  IO.FS.writeFile answers ("\n".intercalate (lines.toList.map (answer env)) ++ "\n")
  return 0
