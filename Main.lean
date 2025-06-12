-- import System.IO
-- import IO.FS
import Pipes
import Pipes.Debug

open IO

namespace Examples

def triple [Monad m] (x : b) : Producer b m PUnit := do
  Proxy.yield x
  Proxy.yield x
  Proxy.yield x

def numbers : List Nat → Producer Nat m PUnit := Proxy.fromList

def filterEven : Pipe Nat Nat m PUnit := Proxy.Unbounded.filter (· % 2 = 0)

def takeThree : Pipe Nat Nat m PUnit := Proxy.take 3

def addTen : Pipe Nat Nat m PUnit := Proxy.Unbounded.mapPipe (· + 10)

partial def toListConsumer [Inhabited a] : Consumer a (StateM (List a)) PUnit :=
  .Request () (fun a => .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

def examplePipeline : Producer String m PUnit :=
  numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    >-> filterEven
    >-> takeThree
    >-> Proxy.Unbounded.mapPipe toString

#guard (Proxy.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] |>.toList) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> takeThree |>.toList) = [1, 2, 3]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven |>.toList) = [2, 4, 6, 8, 10]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven >-> takeThree |>.toList) = [2, 4, 6]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> Proxy.Unbounded.filter (· % 2 = 0) |>.enumerateDownstreamOutput |>.toList) = [(0, 2), (1, 4), (2, 6), (3, 8), (4, 10)]

def stringFoldConsumer : Producer b Id r -> Id (List b) := Proxy.fold (fun acc xb => xb :: acc) id []

-- -- Complete pipeline using your connect operator
-- def completePipeline : Effect (StateM String) Unit :=
--   numberProducer >-> (addTenToString >-> concatConsumer)
--
-- -- Function to run the pipeline and extract result
-- def runPipeline : String :=
--   let result := Proxy.runEffect completePipeline
--   (result.run "").2
--
--
-- end Examples
--
-- -- Example usage:
-- def simpleProducer [Monad m] : Producer Nat m PUnit := do
--   Proxy.respond 1
--   Proxy.respond 2
--   Proxy.respond 3
--   pure ()
--
-- def simpleConsumer [Monad m] : Consumer Nat m PUnit :=
--   Proxy.request () >>= fun n =>
--   -- In a real implementation, you'd do something with n
--   pure ()
--
-- -- Composition example:
-- def simplePipe [Monad m] : Pipe Nat String m PUnit :=
--   Proxy.request () >>= fun n =>
--   Proxy.respond (toString n) >>= fun _ =>
--   pure ()
--
-- -- To run: simpleProducer //> simplePipe //> simpleConsumer
--
-- -- Assume your Proxy definition and associated instances have been imported as above.
--
-- -- Equivalent of Haskell's `stdinLn :: Producer String IO ()`
-- -- In Proxy terms: `Proxy PUnit PUnit Void String IO PUnit`
-- partial def stdinLn : Proxy PUnit PUnit PEmpty String IO PUnit := do
--   eof ← Proxy.monadLift IO.getStdin >>= Proxy.monadLift ∘ IO.FS.Handle.isEof
--   if eof then
--     pure ()
--   else do
--     line ← Proxy.monadLift IO.getLine
--     _ ← Proxy.respond line
--     stdinLn
