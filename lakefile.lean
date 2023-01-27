import Lake
open Lake DSL

package «separationLogic» {
  -- add package configuration options here
}

lean_lib «SeparationLogic» {
  -- add library configuration options here
}

--@[default_target]
--lean_exe «separationLogic» {
--  root := `Main
--}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"724a444a35a78ce1922f5c3626ff618f50976f62"
require dmonad from git "https://github.com/RemyCiterin/DijkstraMonad.git"
