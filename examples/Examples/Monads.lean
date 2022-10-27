import Examples.Support

namespace Monads.Option


book declaration {{{ first }}}
  def first (xs : List α) : Option α :=
    xs[0]?
stop book declaration


book declaration {{{ firstThird }}}
  def firstThird (xs : List α) : Option (α × α) :=
    match xs[0]? with
    | none => none
    | some first =>
      match xs[2]? with
      | none => none
      | some third =>
        some (first, third)
stop book declaration


book declaration {{{ firstThirdFifth }}}
  def firstThirdFifth (xs : List α) : Option (α × α × α) :=
    match xs[0]? with
    | none => none
    | some first =>
      match xs[2]? with
      | none => none
      | some third =>
        match xs[4]? with
        | none => none
        | some fifth =>
          some (first, third, fifth)
stop book declaration


book declaration {{{ firstThirdFifthSeventh }}}
  def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
    match xs[0]? with
    | none => none
    | some first =>
      match xs[2]? with
      | none => none
      | some third =>
        match xs[4]? with
        | none => none
        | some fifth =>
          match xs[6]? with
          | none => none
          | some seventh =>
            some (first, third, fifth, seventh)
stop book declaration

namespace M
book declaration {{{ andThenOption }}}
  def andThen (opt : Option α) (next : α → Option β) : Option β :=
    match opt with
    | none => none
    | some x => next x
stop book declaration


book declaration {{{ firstThirdandThen }}}
  def firstThird (xs : List α) : Option (α × α) :=
    andThen xs[0]? fun first =>
    andThen xs[2]? fun third =>
    some (first, third)
stop book declaration

namespace ExplicitParens
book declaration {{{ firstThirdandThenExpl }}}
  def firstThird (xs : List α) : Option (α × α) :=
    andThen xs[0]? (fun first =>
      andThen xs[2]? (fun third =>
        some (first, third)))
stop book declaration
end ExplicitParens

namespace Fixity
axiom w : Nat
axiom x : Nat
axiom y : Nat
axiom z : Nat

bookExample {{{ plusFixity }}}
  w + x + y + z
  ===>
  (((w + x) + y) + z)
end bookExample

bookExample {{{ powFixity }}}
  w ^ x ^ y ^ z
  ===>
  (w ^ (x ^ (y ^ z)))
end bookExample

bookExample {{{ plusTimesPrec }}}
  x + y * z
  ===>
  x + (y * z)
end bookExample


end Fixity



book declaration {{{ andThenOptArr }}}
  infixl:55 " ~~> " => andThen
stop book declaration



book declaration {{{ firstThirdInfix }}}
  def firstThirdInfix (xs : List α) : Option (α × α) :=
    xs[0]? ~~> fun first =>
    xs[2]? ~~> fun third =>
    some (first, third)
stop book declaration


book declaration {{{ firstThirdFifthSeventInfix }}}
  def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
    xs[0]? ~~> fun first =>
    xs[2]? ~~> fun third =>
    xs[4]? ~~> fun fifth =>
    xs[6]? ~~> fun seventh =>
    some (first, third, fifth, seventh)
stop book declaration
end M

end Monads.Option



namespace Monads.Err

inductive Err (e : Type) (α : Type) where
  | failure : e → Err e α
  | success : α → Err e α

def get (xs : List α) (i : Nat) : Err String α :=
  match xs[i]? with
  | none => Err.failure s!"Index {i} not found (maximum is {xs.length})"
  | some x => Err.success x

def first (xs : List α) : Err String α :=
  get xs 0

def firstThird (xs : List α) : Err String (α × α) :=
  match get xs 0 with
  | Err.failure msg => Err.failure msg
  | Err.success first =>
    match get xs 2 with
    | Err.failure msg => Err.failure msg
    | Err.success third =>
      Err.success (first, third)

def firstThirdFifth (xs : List α) : Err String (α × α × α) :=
  match get xs 0 with
  | Err.failure msg => Err.failure msg
  | Err.success first =>
    match get xs 2 with
    | Err.failure msg => Err.failure msg
    | Err.success third =>
      match get xs 4 with
      | Err.failure msg => Err.failure msg
      | Err.success fifth =>
        Err.success (first, third, fifth)

def firstThirdFifthSeventh (xs : List α) : Err String (α × α × α × α) :=
  match get xs 0 with
  | Err.failure msg => Err.failure msg
  | Err.success first =>
    match get xs 2 with
    | Err.failure msg => Err.failure msg
    | Err.success third =>
      match get xs 4 with
      | Err.failure msg => Err.failure msg
      | Err.success fifth =>
        match get xs 6 with
        | Err.failure msg => Err.failure msg
        | Err.success seventh =>
          Err.success (first, third, fifth, seventh)

def andThen (attempt : Err e α) (next : α → Err e β) : Err e β :=
  match attempt with
  | Err.failure msg => Err.failure msg
  | Err.success x => next x


def firstThird' (xs : List α) : Err String (α × α) :=
  andThen (get xs 0) <|
  fun first  => andThen (get xs 2) <|
  fun third => Err.success (first, third)

infixl:55 " ~~> " => andThen

def ok (x : α) : Err e α := Err.success x

def firstThird'' (xs : List α) : Err String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventh'' (xs : List α) : Err String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)

end Monads.Err

namespace Monads.Writer

def isEven (i : Int) : Bool :=
  i % 2 == 0

example : isEven 34 := by simp
example : ¬isEven 39 := by simp

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def sumAndFindEvens : List Int → WithLog Int Int
  | [] => {log := [], val := 0}
  | i :: is =>
    let {log := moreEven, val := sum } := sumAndFindEvens is
    {log := if isEven i then i :: moreEven else moreEven, val := sum + i}

def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog α β := {log := [], val := x}

def save (data : List α) : WithLog α Unit :=
  {log := data, val := ⟨⟩}

def sumAndFindEvens' : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThen (save (if isEven i then [i] else [])) <|
    fun ⟨⟩ => andThen (sumAndFindEvens is) <|
    fun sum => ok (i + sum)

infixl:55 " ~~> " => andThen

def sumAndFindEvens'' : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    save (if isEven i then [i] else []) ~~> fun ⟨⟩ =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

end Monads.Writer

namespace Monads.State

inductive Tree (α : Type) where
  | leaf : Tree α
  | branch : Tree α → α → Tree α → Tree α
deriving BEq, Hashable, Repr

open Tree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)


def numberFrom (n : Nat) : Tree α → (Nat × Tree (Nat × α))
  | Tree.leaf => (n, Tree.leaf)
  | Tree.branch left x right =>
    let (k, numberedLeft) := numberFrom n left
    let (i, numberedRight) := numberFrom (k+1) right
    (i, Tree.branch numberedLeft (k, x) numberedRight)

def number (t : Tree α) : Tree (Nat × α) := (numberFrom 0 t).snd

#eval number aTree

structure State (σ : Type) (α : Type) where
  run : σ → (σ × α)

def get : State σ σ where
  run s := (s, s)

def set (s : σ) : State σ Unit where
  run _ := (s, ⟨⟩)

def modify (f : σ → σ) : State σ Unit where
  run s := (f s, ⟨⟩)

def andThen (action : State σ α) (next : α → State σ β) : State σ β where
  run s :=
    let (s', x) := action.run s
    (next x).run s'

def ok (x : α) : State σ α where
  run s := (s, x)

infixl:55 " ~~> " => andThen

def number' : Tree α → State Nat (Tree (Nat × α))
  | Tree.leaf => ok Tree.leaf
  | Tree.branch left x right =>
    number' left ~~> fun numberedLeft =>
    get ~~> fun n =>
    modify (· + 1) ~~> fun ⟨⟩ =>
    number' right ~~> fun numberedRight =>
    ok (Tree.branch numberedLeft (n, x) numberedRight)

#eval ((number' aTree).run 0).snd

end Monads.State

namespace Monads.Reader

structure Config where
  useAscii : Bool := false
  currentPrefix := ""

def preFile := "├──"
def preDir := "│  "

def showFile (cfg : Config) (file : String) : IO Unit := do
  IO.println s!"{cfg.currentPrefix} {file}"

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println s!"{cfg.currentPrefix} {dir}/"

def doList : (List α) → (α → IO Unit) → IO Unit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    doList xs action

partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match path.fileName with
  | none => pure ()
  | some name =>
    if !(← path.isDir) then
      showFile cfg name
    else
      showDirName cfg name
      let contents ← path.readDir
      let newConfig := {cfg with currentPrefix := preDir ++ " " ++ cfg.currentPrefix}
      doList contents.toList (fun d =>
        dirTree newConfig d.path)


structure ConfigIO (β : Type) (α : Type) where
  mk ::
  run : β → IO α
deriving Inhabited

def config {β : Type} : ConfigIO β β := ConfigIO.mk (fun x => pure x)

def locally (change : β → γ) (action : ConfigIO γ α) : ConfigIO β α where
  run x := action.run (change x)

def io (action : IO α) : ConfigIO β α where
  run _ := action

def ok (x : α) : ConfigIO β α where
  run _ := pure x

def andThen (first : ConfigIO β α) (next : α → ConfigIO β γ) : ConfigIO β γ where
  run cfg := do
    let res ← first.run cfg
    (next res).run cfg

infixl:55 " ~~> " => andThen

def showFile' (file : String) : ConfigIO Config Unit :=
  config ~~> fun cfg => io (IO.println s!"{cfg.currentPrefix} {file}")

def showDirName' (dir : String) : ConfigIO Config Unit :=
  config ~~> fun cfg => io (IO.println s!"{cfg.currentPrefix} {dir}/")

def doList' : (List α) → (α → ConfigIO β Unit) → ConfigIO β Unit
  | [], _ => ok ()
  | x :: xs, action =>
    action x ~~> fun ⟨⟩ =>
    doList' xs action

def inDir (cfg : Config) : Config :=
  {cfg with currentPrefix := preDir ++ " " ++ cfg.currentPrefix}

partial def dirTree' (path : System.FilePath) : ConfigIO Config Unit :=
  match path.fileName with
  | none => ok ()
  | some name =>
    io path.isDir ~~> fun isDir =>
    if !isDir then
      showFile' name
    else
      showDirName' name ~~> fun ⟨⟩ =>
      io path.readDir ~~> fun (contents : Array IO.FS.DirEntry) =>
      locally inDir (doList' contents.toList (fun d => dirTree' d.path))

end Monads.Reader
