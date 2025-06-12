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

def filterEven : Pipe Nat Nat m PUnit := .Unbounded.filter (· % 2 = 0)

def takeThree : Pipe Nat Nat m PUnit := .take 3

#guard (Proxy.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] |>.toList) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> takeThree |>.toList) = [1, 2, 3]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven |>.toList) = [2, 4, 6, 8, 10]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven >-> takeThree |>.toList) = [2, 4, 6]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven >-> takeThree >-> .Unbounded.mapPipe toString |>.toList) = ["2", "4", "6"]
#guard (.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven |>.enumerateDownstreamOutput |>.toList) = [(0, 2), (1, 4), (2, 6), (3, 8), (4, 10)]

partial def Unbounded.toListConsumer : Consumer a (StateM (List a)) PUnit :=
  .Request () (fun a => .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

#guard (
  let prod := (Proxy.fromList [1, 2, 3, 4, 5] : Producer Nat (StateM (List Nat)) PUnit)
  let (_, s) := Proxy.runEffect (prod >-> Unbounded.toListConsumer) []
  s.reverse
) = [1, 2, 3, 4, 5]

def foldConsumer : Producer b Id PUnit -> List b := Id.run (Proxy.fold (fun acc xb => xb :: acc) List.reverse [])

#guard (foldConsumer (Proxy.fromList [1, 2, 3])) = [1, 2, 3]

-- Equivalent of Haskell's `stdinLn :: Producer String IO ()`
partial def stdinLn : PUnit -> Producer String IO PUnit :=
  -- BAD: let eof detection: `eof := line == ""; if eof then .Respond line stdinLn else .Pure ()`
  fun _ => .M (do (← IO.getStdin).getLine) fun line => .Respond line stdinLn

def main : IO PUnit := do
  Proxy.runEffect (stdinLn ())
