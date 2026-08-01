module
import Expect.Basic
import Expect.Buffer
import Expect.Pty
public import Expect.Run

/-!
Scripted terminal sessions.

A script says which command to run, what the program is expected to write, and what is typed in
response. Running it produces a transcript that records the session as a terminal would show it.
-/
