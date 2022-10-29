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


book declaration {{{ Err }}}
  inductive Err (ε : Type) (α : Type) where
    | failure : ε → Err ε α
    | success : α → Err ε α
  deriving BEq, Hashable, Repr
stop book declaration

namespace Monads.Err


book declaration {{{ getErr }}}
  def get (xs : List α) (i : Nat) : Err String α :=
    match xs[i]? with
    | none => Err.failure s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => Err.success x
stop book declaration


book declaration {{{ ediblePlants }}}
  def ediblePlants : List String :=
    ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
stop book declaration

expect info {{{ success }}}
  #eval get ediblePlants 2
message
  "Err.success \"sea buckthorn\""
end expect

expect info {{{ failure }}}
  #eval get ediblePlants 4
message
  "Err.failure \"Index 4 not found (maximum is 3)\""
end expect


book declaration {{{ firstErr }}}
  def first (xs : List α) : Err String α :=
    get xs 0
stop book declaration


book declaration {{{ firstThirdErr }}}
  def firstThird (xs : List α) : Err String (α × α) :=
    match get xs 0 with
    | Err.failure msg => Err.failure msg
    | Err.success first =>
      match get xs 2 with
      | Err.failure msg => Err.failure msg
      | Err.success third =>
        Err.success (first, third)
stop book declaration


book declaration {{{ firstThirdFifthErr }}}
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
stop book declaration


book declaration {{{ firstThirdFifthSeventhErr }}}
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
stop book declaration


book declaration {{{ andThenErr }}}
  def andThen (attempt : Err e α) (next : α → Err e β) : Err e β :=
    match attempt with
    | Err.failure msg => Err.failure msg
    | Err.success x => next x
stop book declaration

namespace AndThen
book declaration {{{ firstThirdAndThenErr }}}
  def firstThird' (xs : List α) : Err String (α × α) :=
    andThen (get xs 0) fun first  =>
    andThen (get xs 2) fun third =>
    Err.success (first, third)
stop book declaration
end AndThen



book declaration {{{ andThenErrInfix }}}
  infixl:55 " ~~> " => andThen
stop book declaration

book declaration {{{ okErr }}}
  def ok (x : α) : Err ε α := Err.success x
stop book declaration

book declaration {{{ failErr }}}
  def fail (err : ε) : Err ε α := Err.failure err
stop book declaration

namespace Eff
book declaration {{{ getErrEffects }}}
  def get (xs : List α) (i : Nat) : Err String α :=
    match xs[i]? with
    | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => ok x
stop book declaration
end Eff

namespace WithInfix
book declaration {{{ firstThirdInfixErr }}}
  def firstThird (xs : List α) : Err String (α × α) :=
    get xs 0 ~~> fun first =>
    get xs 2 ~~> fun third =>
    ok (first, third)
stop book declaration

book declaration {{{ firstThirdFifthSeventInfixErr }}}
  def firstThirdFifthSeventh (xs : List α) : Err String (α × α × α × α) :=
    get xs 0 ~~> fun first =>
    get xs 2 ~~> fun third =>
    get xs 4 ~~> fun fifth =>
    get xs 6 ~~> fun seventh =>
    ok (first, third, fifth, seventh)
stop book declaration

end WithInfix


end Monads.Err




book declaration {{{ Tree }}}
  inductive Tree (α : Type) where
    | leaf : Tree α
    | branch : Tree α → α → Tree α → Tree α
  deriving BEq, Hashable, Repr
stop book declaration

namespace Monads.Writer


book declaration {{{ isEven }}}
  def isEven (i : Int) : Bool :=
    i % 2 == 0
stop book declaration

example : isEven 34 := by simp
example : ¬isEven 39 := by simp


book declaration {{{ sumAndFindEvensDirect }}}
  def sumAndFindEvens : List Int → List Int × Int
    | [] => ([], 0)
    | i :: is =>
      let (moreEven, sum) := sumAndFindEvens is
      (if isEven i then i :: moreEven else moreEven, sum + i)
stop book declaration

namespace MoreMonadic
book declaration {{{ sumAndFindEvensDirectish }}}
  def sumAndFindEvens : List Int → List Int × Int
    | [] => ([], 0)
    | i :: is =>
      let (moreEven, sum) := sumAndFindEvens is
      let (evenHere, ⟨⟩) := (if isEven i then [i] else [], Unit.unit)
      (evenHere ++ moreEven, sum + i)
stop book declaration
end MoreMonadic

book declaration {{{ preorderSum }}}
  def preorderSum : Tree Int → List Int × Int
    | Tree.leaf => ([], 0)
    | Tree.branch l x r =>
      let (leftVisited, leftSum) := preorderSum l
      let (hereVisited, hereSum) := ([x], x)
      let (rightVisited, rightSum) := preorderSum r
      (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)
stop book declaration


book declaration {{{ WithLog }}}
  structure WithLog (logged : Type) (α : Type) where
    log : List logged
    val : α
stop book declaration


book declaration {{{ andThenWithLog }}}
  def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
stop book declaration


book declaration {{{ okWithLog }}}
  def ok (x : β) : WithLog α β := {log := [], val := x}
stop book declaration


book declaration {{{ save }}}
  def save (data : α) : WithLog α Unit :=
    {log := [data], val := ⟨⟩}
stop book declaration

namespace WithAndThen


book declaration {{{ sumAndFindEvensAndThen }}}
  def sumAndFindEvens : List Int → WithLog Int Int
    | [] => ok 0
    | i :: is =>
      andThen (if isEven i then save i else ok ⟨⟩) fun ⟨⟩ =>
      andThen (sumAndFindEvens is) fun sum =>
      ok (i + sum)
stop book declaration


book declaration {{{ preorderSumAndThen }}}
  def preorderSum : Tree Int → WithLog Int Int
    | Tree.leaf => ok 0
    | Tree.branch l x r =>
      andThen (preorderSum l) fun leftSum =>
      andThen (save x) fun ⟨⟩ =>
      andThen (preorderSum r) fun rightSum =>
      ok (leftSum + x + rightSum)
stop book declaration

end WithAndThen



book declaration {{{ infixAndThenLog }}}
  infixl:55 " ~~> " => andThen
stop book declaration

namespace WithInfix


book declaration {{{ withInfixLogging }}}
  def sumAndFindEvens : List Int → WithLog Int Int
    | [] => ok 0
    | i :: is =>
      (if isEven i then save i else ok ⟨⟩) ~~> fun ⟨⟩ =>
      sumAndFindEvens is ~~> fun sum =>
      ok (i + sum)

  def preorderSum : Tree Int → WithLog Int Int
    | Tree.leaf => ok 0
    | Tree.branch l x r =>
      preorderSum l ~~> fun leftSum =>
      save x ~~> fun ⟨⟩ =>
      preorderSum r ~~> fun rightSum =>
      ok (leftSum + x + rightSum)
stop book declaration

end WithInfix

end Monads.Writer

namespace Monads.State


book declaration {{{ aTree }}}
  open Tree in
  def aTree :=
    branch
      (branch
         (branch leaf "a" (branch leaf "b" leaf))
         "c"
         leaf)
      "d"
      (branch leaf "e" leaf)
stop book declaration



book declaration {{{ numberDirect }}}
  def number (t : Tree α) : Tree (Nat × α) :=
    let rec helper (n : Nat) : Tree α → (Nat × Tree (Nat × α))
      | Tree.leaf => (n, Tree.leaf)
      | Tree.branch left x right =>
        let (k, numberedLeft) := helper n left
        let (i, numberedRight) := helper (k+1) right
        (i, Tree.branch numberedLeft (k, x) numberedRight)
    (helper 0 t).snd
stop book declaration

expect info {{{ numberATree }}}
  #eval number aTree
message
"Tree.branch
  (Tree.branch (Tree.branch (Tree.leaf) (0, \"a\") (Tree.branch (Tree.leaf) (1, \"b\") (Tree.leaf))) (2, \"c\") (Tree.leaf))
  (3, \"d\")
  (Tree.branch (Tree.leaf) (4, \"e\") (Tree.leaf))"
end expect


book declaration {{{ State }}}
  def State (σ : Type) (α : Type) : Type :=
    σ → (σ × α)
stop book declaration


book declaration {{{ get }}}
  def get : State σ σ :=
    fun s => (s, s)
stop book declaration


book declaration {{{ set }}}
  def set (s : σ) : State σ Unit :=
    fun _ => (s, ⟨⟩)
stop book declaration


book declaration {{{ andThenState }}}
  def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
    fun s =>
      let (s', x) := first s
      next x s'

  infixl:55 " ~~> " => andThen
stop book declaration


book declaration {{{ okState }}}
  def ok (x : α) : State σ α :=
    fun s => (s, x)
stop book declaration


namespace Monadicish


book declaration {{{ numberMonadicish }}}
  def number (t : Tree α) : Tree (Nat × α) :=
    let rec helper : Tree α → State Nat (Tree (Nat × α))
      | Tree.leaf => ok Tree.leaf
      | Tree.branch left x right =>
        helper left ~~> fun numberedLeft =>
        get ~~> fun n =>
        set (n + 1) ~~> fun ⟨⟩ =>
        helper right ~~> fun numberedRight =>
        ok (Tree.branch numberedLeft (n, x) numberedRight)
    (helper t 0).snd
stop book declaration

end Monadicish

example : number aTree = Monadicish.number aTree := by rfl

end Monads.State



namespace Monads.Reader -- TODO save me for monad transformer chapter

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
