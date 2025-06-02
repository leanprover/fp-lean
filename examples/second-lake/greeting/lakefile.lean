import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"


package greeting {
  -- add package configuration options here
}

@[default_target]
lean_lib Greeting

@[default_target]
lean_lib Aux

@[default_target]
lean_exe greeting {
  root := `Main
}
