import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"

package examples {
  -- add configuration options here
}

@[default_target]
lean_lib SimpleHello where
  srcDir := "simple-hello"
  roots := #[`Hello]

@[default_target]
lean_lib HelloName where
  srcDir := "hello-name"
  roots := #[`HelloName]


@[default_target]
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

@[default_target]
lean_exe sort {
  root := `Examples.ProgramsProofs.InstrumentedInsertionSort
}
