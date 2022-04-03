import Init.Coe

def Char.digit? (char : Char) : Option Nat :=
  if char.isDigit then
    some (char.toNat - '0'.toNat)
  else
    none

-- TODO this is grossly inefficient
def trim (str : String) : String :=
  String.mk ((str.data.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

def lookup [BEq k] : (key : k) -> (options : List (k × v)) -> Option v
  | key, [] => none
  | key, (key', v) :: options =>
    if key == key'
      then some v
      else lookup key options

def stringToNat (str : String) : Option Nat := Id.run <| do
  let mut n : Nat := 0
  if str == "" then return none
  for d in str.data do
    match d.digit? with
      | some k => n := n * 10 + k
      | none => return none
  return n

def stringToInt (str : String) : Option Int :=
  match str.data with
    | [] => none
    | '+'::ds => OptionM.run do pure (Int.ofNat (<- stringToNat { data := ds }))
    | '-'::ds => OptionM.run do pure (Int.negOfNat (<- stringToNat { data := ds }))
    | other => Int.ofNat <$> stringToNat str
