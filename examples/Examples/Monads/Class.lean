import Examples.Support
import Examples.Monads

namespace Class
book declaration {{{ FakeMonad }}}
  class Monad (m : Type → Type) where
    pure : α → m α
    bind : m α → (α → m β) → m β
stop book declaration
end Class



book declaration {{{ firstThirdFifthSeventhMonad }}}
  def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
    lookup xs 0 >>= fun first =>
    lookup xs 2 >>= fun third =>
    lookup xs 4 >>= fun fifth =>
    lookup xs 6 >>= fun seventh =>
    pure (first, third, fifth, seventh)
stop book declaration

def slowMammals : List String := ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
