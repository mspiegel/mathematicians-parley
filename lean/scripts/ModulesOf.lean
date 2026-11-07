import Mathlib
import Mathlib.Tactic.MinImports
import Lean.Elab.Frontend

/-!
# The modules a Parley build's Lean names come from

`parley build lean` asks, for each constant and each piece of syntax its
files write, which modules declare it, so that a file imports those and
not the whole of Mathlib. It caches the answers against the Mathlib
revision, and runs this only for keys the cache lacks:

    lake env lean --run scripts/ModulesOf.lean <asked> <answers>

Each line of `<asked>` is a JSON object with a `kind` and a `key`:

* `const` and a constant's full name: its module, and those of the
  `norm_num` and `positivity` extensions keyed on it;
* `term` or `tactic` and a sample of syntax, parsed in that category: the
  modules of its syntax kinds and of the constants it names, and of a
  term's those it uses once elaborated;
* `command` and a declaration: the modules of its syntax kinds and of the
  constants it uses once elaborated.

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

/-- A `norm_num` or `positivity` extension: the constants of one pattern
it is keyed on, and the module declaring it. -/
structure Taught where
  keys : NameSet
  module : Name

/-- Every pattern of every `norm_num` and `positivity` extension: what
teaches those tactics about the constants it names, `Nat.Prime` the
extension that decides primality. -/
def extensionTable (env : Environment) : Array Taught := Id.run do
  let mut out : Array Taught := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    let mut keyss : Array (Array (Array Meta.DiscrTree.Key)) := #[]
    for e in Mathlib.Meta.NormNum.normNumExt.ext.getModuleEntries env (i : ModuleIdx) do
      match e with
      | .global (kss, _) | .scoped _ (kss, _) => keyss := keyss.push kss
    for (kss, _) in Mathlib.Meta.Positivity.positivityExt.getModuleEntries env (i : ModuleIdx) do
      keyss := keyss.push kss
    for kss in keyss do
      for ks in kss do
        let keys := ks.foldl (init := ({} : NameSet)) fun s k =>
          match k with
          | .const c _ => s.insert c
          | _ => s
        out := out.push { keys, module := m }
  return out

/-- The constants a term sample uses once elaborated, the instances its
types take included, `Finset.Icc (sorry : ℤ) (sorry : ℤ)` taking `ℤ`'s
`LocallyFiniteOrder`; none where it does not elaborate, its parse being
all there is of it. -/
def elaborated (env : Environment) (stx : Syntax) : IO NameSet := do
  let ctx : Core.Context := { fileName := "<sample>", fileMap := default }
  let act : MetaM Expr := Elab.Term.TermElabM.run' do
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  try
    let (e, _) ← (act.run' {} {}).toIO ctx { env }
    return e.getUsedConstantsAsSet
  catch _ =>
    return {}

/-- The constants a declaration uses, its statement and its proof as Lean
elaborates them, `simp`'s lemmas and the instances its types take
included: a record's own proof, which names little of what it uses. -/
def declared (env : Environment) (command : String) : IO (Except String NameSet) := do
  -- Elaborated in order, so that each theorem's proof is there to read
  -- when it is read, not a task still running.
  let opts := ({} : Options).setBool `Elab.async false
  let (after, log) ← Lean.Elab.process command env opts
  if log.hasErrors then
    let first ← (log.toList.find? (·.severity == .error)).mapM (·.toString)
    return .error (first.getD "it does not elaborate")
  let added := after.constants.map₂.foldl (fun (s : NameSet) n _ => s.insert n) {}
  let used := added.foldl (init := ({} : NameSet)) fun s n =>
    match after.find? n with
    | some info =>
      -- A theorem's proof, which `value?` does not give.
      let value := match info with
        | .thmInfo t => some t.value
        | other => other.value?
      let fromValue := value.map (·.getUsedConstantsAsSet) |>.getD {}
      (s.append info.type.getUsedConstantsAsSet).append fromValue
    | none => s
  return .ok used

/-- The modules declaring the names, and those of the extensions whose
pattern names nothing else (`extensionTable`): the ordinals' `+` is keyed
on `HAdd.hAdd` and `Ordinal`, and teaches nothing to a file of integers.
Lean's own are left out, in order. -/
def modulesTaught (env : Environment) (ext : Array Taught) (names : NameSet) : Array Name :=
  let teaching := ext.filter (fun t => !t.keys.isEmpty && t.keys.all (names.contains ·))
    |>.map (·.module)
  let all := (modulesOf env names ++ teaching).filter (!builtIn ·)
  (all.foldl (fun (s : NameSet) m => s.insert m) {}).toArray.qsort Name.lt

/-- The modules a key names, or why it names none. -/
def modulesFor (env : Environment) (ext : Array Taught) (kind key : String) :
    IO (Except String (Array Name)) := do
  if kind == "const" then
    return .ok (modulesTaught env ext (({} : NameSet).insert key.toName))
  if kind == "command" then
    let kinds := match Parser.runParserCategory env `command key with
      | .ok stx => getSyntaxNodeKinds stx
      | .error _ => {}
    return match ← declared env key with
      | .ok used => .ok (modulesTaught env ext (kinds.append used))
      | .error e => .error e
  match Parser.runParserCategory env kind.toName key with
  | .error e => return .error e
  | .ok stx =>
    let used ← if kind == "term" then elaborated env stx else pure {}
    return .ok (modulesTaught env ext ((getSyntaxNodeKinds stx).append used))

/-- The answer line for one asked line. -/
def answer (env : Environment) (ext : Array Taught) (line : String) :
    IO String := do
  let asked : Except String (String × String) := do
    let j ← Json.parse line
    return (← j.getObjValAs? String "kind", ← j.getObjValAs? String "key")
  match asked with
  | .error e => return (Json.mkObj [("line", line), ("error", e)]).compress
  | .ok (kind, key) =>
    let found := match ← modulesFor env ext kind key with
      | .ok ms => ("modules", toJson (ms.map toString))
      | .error e => ("error", toJson e)
    return (Json.mkObj [("kind", kind), ("key", key), found]).compress

unsafe def main (args : List String) : IO UInt32 := do
  let [asked, answers] := args
    | IO.eprintln "usage: ModulesOf <asked> <answers>"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- The bridges too, which a record's own proof may name; the build takes
  -- a file's bridges from its trees, never from these answers.
  let env ← importModules #[{ module := `Mathlib }, { module := `LeanBridges }] {}
    (loadExts := true)
  let lines := (← IO.FS.lines asked).filter (· ≠ "")
  let ext := extensionTable env
  let out ← lines.toList.mapM (answer env ext)
  IO.FS.writeFile answers ("\n".intercalate out ++ "\n")
  return 0
