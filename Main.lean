-- import System.IO
import IO.FS
import Pipes

open IO

-- Assume your Proxy definition and associated instances have been imported as above.

-- Equivalent of Haskell's `stdinLn :: Producer String IO ()`
-- In Proxy terms: `Proxy Unit Unit Void String IO Unit`
partial def stdinLn : Proxy Unit Unit Empty String IO Unit := do
  eof ← Proxy.monadLift IO.getStdin >>= Proxy.monadLift ∘ IO.FS.Handle.isEof
  if eof then
    pure ()
  else do
    line ← Proxy.monadLift IO.getLine
    _ ← Proxy.respond line
    stdinLn
