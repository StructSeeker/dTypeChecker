import Lake
open Lake DSL

package «dTypeChecker» where
  -- add package configuration options here

lean_lib «DTypeChecker» where
  -- add library configuration options here

@[default_target]
lean_exe «dtypechecker» where
  root := `Main
