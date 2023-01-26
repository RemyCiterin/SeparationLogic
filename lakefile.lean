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

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"f759a3662ca93422c3c8281852dc352f9a7b5399"
require dmonad from git "https://github.com/RemyCiterin/DijkstraMonad.git"
