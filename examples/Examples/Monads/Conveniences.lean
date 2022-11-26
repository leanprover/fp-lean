import Examples.Support
import Examples.Classes

namespace Old
book declaration {{{ equalHuhOld }}}
  def equal? [BEq α] (x : α) (y : α) : Option α :=
    if x == y then
      some x
    else
      none
stop book declaration
end Old


namespace New
book declaration {{{ equalHuhNew }}}
  def equal? [BEq α] (x y : α) : Option α :=
    if x == y then
      some x
    else
      none
stop book declaration
end New

example [BEq α] : Old.equal? (α := α) = New.equal? := by rfl

namespace Old

book declaration {{{ mirrorOld }}}
  def BinTree.mirror : BinTree α → BinTree α
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
stop book declaration
end Old


namespace New
book declaration {{{ mirrorNew }}}
  def BinTree.mirror : BinTree α → BinTree α
    | .leaf => .leaf
    | .branch l x r => .branch (mirror r) x (mirror l)
stop book declaration
end New
