import Lake

open System Lake DSL

package book where
  version := v!"0.1.0"
  leanOptions :=
  #[⟨`weak.verso.examples.suggest, true⟩,
    ⟨`weak.linter.verso.manual.headerTags, true⟩,
    ⟨`weak.verso.externalExamples.suppressedNamespaces,
      "A Adding Agh Argh Almost Alt AltPos AndDef AndThen AppendOverloads ApplicativeOptionLaws ApplicativeOptionLaws2 ApplicativeToFunctor Apply Argh AutoImpl B BadUnzip BetterHPlus BetterPlicity Blurble Both Busted C CheckFunctorPair Class Cls Cmp Connectives Cont Ctor D Decide Demo Desugared Details DirTree DirTree.Old DirTree.Readerish DirTree.T Double EEE EarlyReturn Eff Errs Eta Evaluator Even Ex Exercises Explicit ExplicitParens Extra Extras F F1 F2 Fake FakeAlternative FakeCoe FakeExcept FakeFunctor FakeMonad FakeOrElse FakeSeqRight FancyDo FastPos FinDef Finny Fixity Floop ForMIO Foo Foo2 Four FourPointFive Golf Golf' Guard H HelloName1 HelloName2 HelloName3 Huh IdentMonad Impl Improved Inductive Inflexible IterSub L Lawful ListExtras Loops Loops.Cont M MMM Main1 Main2 Main3 Match MatchDef Mine Modify MonadApplicative MonadApplicativeDesugar MonadApplicativeProof1 MonadApplicativeProof2 MonadApplicativeProof3 MonadApplicativeProof4 MonadLaws Monadicish Monads.Err Monads.Option Monads.State Monads.Writer More MoreClear MoreMonadic Mut MyList1 MyList15 MyList3 MyListStuff MyMonadExcept MyMonadLift MySum NRT NT NatLits Nested New NoTac Non Numbering Numbering.Short Old One OneAttempt Oooops Ooops Oops Opt Option OrElse Orders Original Other OverloadedBits OverloadedInt OwnInstances Partial PipelineEx PointStuff ProblematicHPlus Prod Proofs PropStuff Provisional Provisional2 R Ranges Readerish ReallyNoTypes Reorder SameDo SeqCounterexample SeqLeftSugar SeqRightSugar Ser Short St StEx StdLibNoUni Str StructNotation Structed SubtypeDemo SugaryOrElse Sum T TTT Tactical TailRec Temp ThenDoUnless Three Transformed Two U Up UseList VariousTypes Verbose Wak Whatevs WithAndThen WithDo WithFor WithInfix WithMatch WithPattern"⟩]

require verso from git "https://github.com/leanprover/verso.git"@"main"

private def examplePath : System.FilePath := "../examples"

private def lakeVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LAKE_CACHE_DIR",
    "LEAN", "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

private def fixPath (path : System.SearchPath) : String :=
  path |>.map (·.toString) |>.filter (!·.contains ".lake") |> System.SearchPath.separator.toString.intercalate

input_dir examples where
  path := examplePath
  text := true
  filter := .extension "lean"

input_dir exampleBinaries where
  path := examplePath / ".lake" / "build" / "bin"
  text := false


target buildExamples (pkg) : Unit := do
  let exs ← examples.fetch
  let exBins ← exampleBinaries.fetch
  let toolchainFile := examplePath / "lean-toolchain"
  let toolchain ← IO.FS.readFile toolchainFile
  let toolchain := toolchain.trimAscii |>.dropPrefix "leanprover/lean4:" |>.dropPrefix "v" |>.copy
  addPureTrace toolchain
  exBins.bindM fun binFiles => do
    for file in binFiles do
      if file.extension.isNone || file.extension.isEqSome System.FilePath.exeExtension then
        addTrace (← computeTrace file)
    exs.mapM fun exFiles => do
      let mut list := ""
      for file in exFiles do
        addTrace (← computeTrace <| TextFilePath.mk file)
        list := list ++ s!"{file}\n"
      buildFileUnlessUpToDate' (pkg.buildDir / "examples-built") (text := true) do
        Lake.logInfo s!"Building examples in {examplePath}"
        let mut out := ""
        let path := fixPath (← getSearchPath "PATH")
        out := out ++ (← captureProc {
          cmd := "elan",
          args := #["run", "--install", toolchain, "lake", "build"],
          cwd := examplePath,
          env := lakeVars.map (·, none) ++ #[("PATH", some path)]
        })
        out := out ++ (← captureProc {
          cmd := "elan",
          args := #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"],
          cwd := examplePath,
          env := lakeVars.map (·, none) ++ #[("PATH", some path)]
        })
        IO.FS.createDirAll pkg.buildDir
        IO.FS.writeFile (pkg.buildDir / "examples-built") (list ++ "--- Output ---\n" ++ out)

target syncBuildExamples : Unit := do
  .pure <$> (← buildExamples.fetch).await

lean_lib FPLean where
  needs := #[syncBuildExamples]

@[default_target] lean_exe «fp-lean» where root := `Main
