-- import System.IO
-- import IO.FS
import Pipes

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

def enumerateNat : Pipe Nat (Nat × Nat) m PUnit := Proxy.enumerate

partial def toListConsumer [Inhabited a] : Consumer a (StateM (List a)) PUnit :=
  .Request () (fun a =>
    .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

def examplePipeline : Producer String m PUnit :=
  numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    >-> filterEven
    >-> takeThree
    >-> Proxy.Unbounded.mapPipe toString

inductive ASM.{u} (a' a b' b r : Type u) where
  | ReqInput : a' -> ASM a' a b' b r
  | ReqKArg  : a -> ASM a' a b' b r
  | ResInput : b -> ASM a' a b' b r
  | ResKArg  : b' -> ASM a' a b' b r
  | SomeEffect : ASM a' a b' b r
  | Pure : r -> ASM a' a b' b r
  deriving BEq, DecidableEq, Ord, Inhabited, Repr

def debugProducer { b r : Type 0 } :  Producer b Id r → List (ASM PEmpty PUnit PUnit b r)
  | .Request v _ => PEmpty.elim v
  | .Respond b k => .ResInput b :: .ResKArg .unit :: debugProducer (k .unit)
  | .M mx k      => .SomeEffect :: debugProducer (k (Id.run mx))
  | .Pure r      => [.Pure r]

def debugWithInputs
    (inputs : List a) (outputs : List b')
    : Proxy a' a b' b Id r → List (ASM a' a b' b r) :=
  go inputs outputs []
where
  go : List a → List b' → List (ASM a' a b' b r) → Proxy a' a b' b Id r → List (ASM a' a b' b r)
  | ins, outs, acc, .Request a' k =>
      match ins with
      | i :: ins' =>
          let next := k i
          go ins' outs (acc ++ [.ReqInput a', .ReqKArg i]) next
      | [] => acc ++ [.ReqInput a']  -- no more input to feed
  | ins, outs, acc, .Respond b k =>
      match outs with
      | o :: outs' =>
          let next := k o
          go ins outs' (acc ++ [.ResInput b, .ResKArg o]) next
      | [] => acc ++ [.ResInput b]
  | ins, outs, acc, .M mx mk =>
    let x := Id.run mx
    let next := mk x
    go ins outs (acc ++ [.SomeEffect]) next
  | _, _, acc, .Pure r => acc ++ [.Pure r]

instance : Repr PEmpty where
  reprPrec x _ := nomatch x

#guard Proxy.toList (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval debugProducer (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
#eval debugProducer (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> takeThree)
#eval Proxy.toList (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> takeThree)
-- #eval Proxy.toList (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> Proxy.Unbounded.mapPipe (· + 10))
#eval Proxy.toList (b := Nat) (Proxy.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> Proxy.Fueled.mapPipe .unit 2 (· + 10))
#guard Proxy.toList (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> takeThree) = [1, 1, 1] -- should be [1, 2, 3]

-- #eval Proxy.toList (b := Nat) (numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] >-> filterEven)

-- def stringFoldConsumer : _ := Proxy.fold (fun acc s => s :: acc) id []

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
