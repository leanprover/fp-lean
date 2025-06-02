import Lake
open Lake DSL


package «earlyreturn» {
  -- add package configuration options here
}


@[default_target]
lean_exe «earlyreturn» {
  root := `EarlyReturn
}
