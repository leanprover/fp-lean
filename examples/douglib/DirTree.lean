import ExampleSupport

def String.separate := String.intercalate

-- ANCHOR: compareEntries'
def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
-- ANCHOR_END: compareEntries'

namespace DirTree

-- ANCHOR: names
example := System.FilePath.components
-- ANCHOR_END: names

-- ANCHOR: Config
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
-- ANCHOR_END: Config


-- ANCHOR: filenames
def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
-- ANCHOR_END: filenames


-- ANCHOR: inDirectory
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
-- ANCHOR_END: inDirectory

-- ANCHOR: configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
-- ANCHOR_END: configFromArgs


-- ANCHOR: usage
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
-- ANCHOR_END: usage


-- ANCHOR: Entry
inductive Entry where
  | file : String → Entry
  | dir : String → Entry
-- ANCHOR_END: Entry


-- ANCHOR: toEntry
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))
-- ANCHOR_END: toEntry


-- ANCHOR: doList
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action
-- ANCHOR_END: doList

namespace Old


-- ANCHOR: OldShowFile
def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println (cfg.dirName dir)
-- ANCHOR_END: OldShowFile

-- ANCHOR: OldDirTree
partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName cfg name
  | some (.dir name) =>
    showDirName cfg name
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList (contents.qsort dirLT).toList fun d =>
      dirTree newConfig d.path
-- ANCHOR_END: OldDirTree

-- ANCHOR: OldMain
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
-- ANCHOR_END: OldMain

-- #eval main ["--ascii"]


end Old

namespace Readerish


-- ANCHOR: ConfigIO
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg
-- ANCHOR_END: ConfigIO


-- ANCHOR: ConfigIORun
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
-- ANCHOR_END: ConfigIORun

-- ANCHOR: currentConfig
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
-- ANCHOR_END: currentConfig


-- ANCHOR: locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
-- ANCHOR_END: locally


-- ANCHOR: runIO
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action
-- ANCHOR_END: runIO


-- ANCHOR: MedShowFileDir
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
-- ANCHOR_END: MedShowFileDir

-- ANCHOR: MedDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← runIO path.readDir
      locally (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
-- ANCHOR_END: MedDirTree


-- ANCHOR: MedMain
def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
-- ANCHOR_END: MedMain

end Readerish

namespace MyMonadLift
-- ANCHOR: MyMonadLift
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
-- ANCHOR_END: MyMonadLift
end MyMonadLift

similar datatypes DirTree.MyMonadLift.MonadLift MonadLift

namespace T

-- These are replicated here to make sure we don't forget any important declarations
-- ANCHOR: MyReaderT
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
-- ANCHOR_END: MyReaderT


-- ANCHOR: MonadMyReaderT
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env
-- ANCHOR_END: MonadMyReaderT

namespace R
-- ANCHOR: MyReaderTread
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
-- ANCHOR_END: MyReaderTread
end R


-- ANCHOR: MonadReader
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u + 1) v) where
  read : m ρ

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

export MonadReader (read)
-- ANCHOR_END: MonadReader




-- ANCHOR: ReaderTConfigIO
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α
-- ANCHOR_END: ReaderTConfigIO


-- ANCHOR: MonadLiftReaderT
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action
-- ANCHOR_END: MonadLiftReaderT


-- ANCHOR: showFileAndDir
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"
-- ANCHOR_END: showFileAndDir


-- ANCHOR: MyMonadWithReader
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α
-- ANCHOR_END: MyMonadWithReader


-- ANCHOR: exportWithReader
export MonadWithReader (withReader)
-- ANCHOR_END: exportWithReader


-- ANCHOR: ReaderTWithReader
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)
-- ANCHOR_END: ReaderTWithReader

-- ANCHOR: readerTDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      withReader (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
-- ANCHOR_END: readerTDirTree

-- ANCHOR: NewMain
def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      dirTree (← IO.currentDir) config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
-- ANCHOR_END: NewMain
end T

end DirTree

similar datatypes DirTree.T.MonadWithReader MonadWithReader
