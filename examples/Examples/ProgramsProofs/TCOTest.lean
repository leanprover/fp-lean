import Examples.ProgramsProofs.TCO

def main : IO Unit := do
  let stdout ← IO.getStdout
  IO.println "Start"
  stdout.flush
  let theBigList := bigList 100000000 []
  IO.println "One"
  stdout.flush
  IO.println theBigList.length
  IO.println (Tail.sum theBigList)
  -- IO.println "Two"
  -- stdout.flush
  -- IO.println (NonTail.sum theBigList)
