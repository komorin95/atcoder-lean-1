import Lake

open System Lake DSL

package «atcoder-lean-1» where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.22.0"

require Regex from git "https://github.com/pandaman64/lean-regex"@"v4.22.0"/"regex"

require "fgdorais" / Parser @ git "617f4fa5c48f35076274d57546884261560f1285"

@[default_target] lean_exe «atcoder-lean-1» where root := `Main

def io_examples : List (String × String) := [
  (
    r#"3 34
1
8 13 26
"#,
    r#"13
"#,
  ),
  (
    r#"7 45
2
7 11 16 20 28 34 38
"#,
    r#"12
"#,
  ),
  (
    r#"3 100
1
28 54 81
"#,
    r#"46
"#,
  ),
  (
    r#"3 100
2
28 54 81
"#,
    r#"26
"#,
  ),
  (
    r#"20 1000
4
51 69 102 127 233 295 350 388 417 466 469 523 553 587 720 739 801 855 926 954
"#,
    r#"170
"#,
  )
]

/-
  Test the binary against the examples defined as io_examples above.
  The binary is assumed to be already built and up-to-date.
  ref: https://zenn.dev/qwjyh/articles/17dbe5844bbb48

  TODO: Find a good way to build the binary. Maybe by 'fetch' func?
-/
@[test_driver]
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
