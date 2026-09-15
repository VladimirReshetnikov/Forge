import Lake
open Lake DSL
package forge_extensions
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "1cf325a0cf67aca2b04d76b5380ff6a9e410aefa"
lean_lib ForgeExtensions
