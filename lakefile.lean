import Lake

open System Lake DSL

package «atcoder-lean-1» where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.22.0"

require Regex from git "https://github.com/pandaman64/lean-regex"@"v4.22.0"/"regex"

require "fgdorais" / Parser @ git "617f4fa5c48f35076274d57546884261560f1285"

@[default_target] lean_exe «atcoder-lean-1» where root := `Main
