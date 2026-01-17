import Lake

open System Lake DSL

package «atcoder-lean-1» where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.22.0"

require Regex from git "https://github.com/pandaman64/lean-regex"@"v4.22.0"/"regex"

require "fgdorais" / Parser @ git "617f4fa5c48f35076274d57546884261560f1285"

@[default_target] lean_exe «atcoder-lean-1» where root := `Main

def io_examples : List (String × String) := [
  (
    r#"3 4
"#,
    r#"Even
"#,
  ),
  (
    r#"1 21
"#,
    r#"Odd
"#,
  )
]

/-
  Test the binary against the examples defined as io_examples above.
  The binary is assumed to be already built and up-to-date.
  ref: https://zenn.dev/qwjyh/articles/17dbe5844bbb48

  TODO: Find a good way to build the binary. Maybe by 'fetch' func?
-/
script io_test do
  let this_package := «atcoder-lean-1»
  let fetched ← this_package.get
  let exepath := fetched.file
  IO.println s!"Testing the binary {exepath}"
  for (input, output) in io_examples do
    let spawnArgs : IO.Process.SpawnArgs :=
      ⟨{stdin := .piped, stdout := .piped, stderr := .inherit},
        exepath.toString, #[], none, #[], false, false ⟩
    let proc ← IO.Process.spawn spawnArgs
    proc.stdin.putStr input
    let _ ← proc.takeStdin
    let actualOutput ← proc.stdout.readToEnd
    if output != actualOutput then
      IO.println "Error: for an input example"
      IO.println input
      IO.println "the binary gave the output"
      IO.println actualOutput
      IO.println "while the expected output is"
      IO.println output
      return 1
  return 0
