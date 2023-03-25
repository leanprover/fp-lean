import Lake
open Lake DSL

package examples {
  -- add configuration options here
}

lean_lib Examples {
  -- add lib config here
}

@[default_target]
lean_exe examples {
  root := `Main
}

@[default_target]
lean_exe doug {
  root := `Examples.Doug1
}

@[default_target]
lean_exe tco {
  root := `Examples.ProgramsProofs.TCOTest
}
