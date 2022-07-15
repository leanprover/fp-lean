import Examples.Support

namespace Str

book declaration {{{ Stream }}}
  structure Stream where
    isEof   : IO Bool
    flush   : IO Unit
    read    : USize → IO ByteArray
    write   : ByteArray → IO Unit
    getLine : IO String
    putStr  : String → IO Unit
stop book declaration

end Str

similar datatypes Str.Stream IO.FS.Stream
