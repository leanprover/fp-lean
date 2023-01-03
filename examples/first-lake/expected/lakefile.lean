import Lake
open Lake DSL

package «greeting» {
  -- add package configuration options here
}

lean_lib «Greeting» {
  -- add library configuration options here
}

@[default_target]
lean_exe «greeting» {
  root := `Main
}
