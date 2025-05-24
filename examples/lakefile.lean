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
lean_lib ExampleSupport

@[default_target]
lean_lib Examples

@[default_target]
lean_lib FelineLib {
  srcDir := "feline/2"
  roots := #[`FelineLib]
}

@[default_target]
lean_lib EarlyReturn where
  srcDir := "early-return"

@[default_target]
lean_exe ForMIO where


@[default_target]
lean_exe feline {
  srcDir := "feline/2"
  root := `Main
}

@[default_target]
lean_exe examples {
  root := `Main
}

@[default_target]
lean_lib DougLib where
  srcDir := "douglib"
  roots := #[`DirTree]

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
