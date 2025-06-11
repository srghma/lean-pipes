-- import System.IO
import IO.FS
import Pipes

open IO

namespace Examples

def triple [Monad m] (x : a) : Producer b m Unit := do
  Proxy.yield x
  Proxy.yield x
  Proxy.yield x

def numbers : List Nat → Producer Nat m Unit := Proxy.fromList

def filterEven : Pipe Nat Nat m Unit := Proxy.filter (· % 2 = 0)

def takeThree : Pipe Nat Nat m Unit := Proxy.take 3

def addTen : Pipe Nat Nat m Unit := Proxy.mapPipe (· + 10)

def enumerateNat : Pipe Nat (Nat × Nat) m Unit := Proxy.enumerate

partial def toListConsumer [Inhabited a] : Consumer a (StateM (List a)) Unit :=
  .Request () (fun a =>
    .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

-- def examplePipeline : Producer String m Unit :=
--   numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
--     //> filterEven
--     //> takeThree
--     //> Proxy.mapPipe toString

end Examples

-- Example usage:
def simpleProducer [Monad m] : Producer Nat m Unit :=
  respond 1 >>= fun _ =>
  respond 2 >>= fun _ =>
  respond 3 >>= fun _ =>
  pure ()

def simpleConsumer [Monad m] : Consumer Nat m Unit :=
  request () >>= fun n =>
  -- In a real implementation, you'd do something with n
  pure ()

-- Composition example:
def simplePipe [Monad m] : Pipe Nat String m Unit :=
  request () >>= fun n =>
  respond (toString n) >>= fun _ =>
  pure ()

-- To run: simpleProducer //> simplePipe //> simpleConsumer

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
