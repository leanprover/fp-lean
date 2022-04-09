import Examples.Support

bookExample {{{ three }}}
  1 + 2
  ===>
  3
end bookExample

bookExample {{{ stringAppend }}}
  String.append "it is " (if 1 > 2 then "yes" else "no")
  ===>
  "it is no"
end bookExample
