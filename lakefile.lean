import Lake
open Lake DSL

package "tpl" where
  -- add package configuration options here

lean_lib «Tpl» where
  -- add library configuration options here

@[default_target]
lean_exe "tpl" where
  root := `Main
