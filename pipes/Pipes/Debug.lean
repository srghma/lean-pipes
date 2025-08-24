module
import Pipes.Internal
import Pipes.Core

namespace Pipes.Debug

inductive ASM.{u} (a' a b' b r : Type u) where
  | ReqInput : a' -> ASM a' a b' b r
  | ReqKArg  : a -> ASM a' a b' b r
  | ResInput : b -> ASM a' a b' b r
  | ResKArg  : b' -> ASM a' a b' b r
  | SomeEffect : ASM a' a b' b r
  | Pure : r -> ASM a' a b' b r
  deriving BEq, DecidableEq, Ord, Inhabited, Repr

def debugProducer : Producer b Id r → List (ASM PEmpty PUnit PUnit b r)
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
