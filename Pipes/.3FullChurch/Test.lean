import Pipes.Basic

-- Producer that creates 5 numbers and stops
def numberProducer : Producer Nat Id Unit :=
  fun _ka kb _km kp =>
    kb 1 (fun _ =>
    kb 2 (fun _ =>
    kb 3 (fun _ =>
    kb 4 (fun _ =>
    kb 5 (fun _ =>
    kp ())))))

-- Alternative using fromList (more idiomatic)
def numberProducer' : Producer Nat Id Unit :=
  Proxy.fromList [1, 2, 3, 4, 5]

-- Pipe that takes Nat, adds 10, converts to String
def addTenToString : Pipe Nat String Id Unit :=
  fun ka kb _km kp =>
    ka () (fun n =>
      kb (toString (n + 10)) (fun _ =>
        addTenToString ka kb (fun _ f mt => f mt) kp))

-- Alternative using mapM (if you had it working)
def addTenToString' : Pipe Nat String Id Unit :=
  Proxy.mapM (fun n => pure (toString (n + 10)))

-- Consumer that concatenates all strings
def concatConsumer : Consumer String (StateM String) Unit :=
  fun ka _kb km kp =>
    ka () (fun s =>
      km Unit (fun _ => concatConsumer ka (fun x _ => Empty.elim x) km kp)
             (modify (fun acc => acc ++ s)))

-- Alternative consumer that returns the final result
partial def concatConsumer' : Consumer String (StateM String) String :=
  fun ka _kb km kp =>
    ka () (fun s =>
      km Unit (fun _ =>
        km String kp (do
          modify (fun acc => acc ++ s)
          get))
        (modify (fun acc => acc ++ s)))

-- Simple fold-based consumer (more direct)
def stringFoldConsumer : Consumer String Id (List String) :=
  Proxy.fold (fun acc s => s :: acc) []

-- Complete pipeline using your connect operator
def completePipeline : Effect (StateM String) Unit :=
  numberProducer >-> (addTenToString >-> concatConsumer)

-- Function to run the pipeline and extract result
def runPipeline : String :=
  let result := Proxy.runEffect completePipeline
  (result.run "").2

-- Example usage and testing
namespace PipelineTests

-- Test individual components
def testProducer : List Nat :=
  let collectConsumer : Consumer Nat Id (List Nat) :=
    Proxy.fold (fun acc n => n :: acc) []
  Id.run $ Proxy.runEffect (numberProducer >-> collectConsumer)

def testPipe : List String :=
  let testInput : Producer Nat Id Unit := Proxy.fromList [1, 2, 3]
  let collectStrings : Consumer String Id (List String) :=
    Proxy.fold (fun acc s => s :: acc) []
  Id.run $ Proxy.runEffect (testInput >-> (addTenToString >-> collectStrings))

-- Expected results:
-- testProducer should give [5, 4, 3, 2, 1] (reversed due to fold)
-- testPipe should give ["13", "12", "11"] (reversed)
-- runPipeline should give "1112131415"

end PipelineTests

-- More idiomatic version using your existing combinators
namespace IdomaticVersion

-- Using fromList for producer
def producer : Producer Nat Id Unit := Proxy.fromList [1, 2, 3, 4, 5]

-- Using mapM for transformation (if available)
def transformPipe : Pipe Nat String Id Unit :=
  fun ka kb km kp =>
    ka () (fun n =>
      kb (toString (n + 10)) (fun _ =>
        transformPipe ka kb km kp))

-- Using fold for consumer
def consumer : Consumer String Id String :=
  Proxy.fold (fun acc s => acc ++ s) ""

-- Complete pipeline
def pipeline : Effect Id String :=
  producer >-> (transformPipe >-> consumer)

def result : String := Id.run (Proxy.runEffect pipeline)

-- This should produce "1112131415"

end IdomaticVersion

-- Using the composition operators from your code
namespace CompositionExample

def producer := Proxy.fromList [1, 2, 3, 4, 5]
def transform : Nat → Pipe Nat String Id Unit :=
  fun _ => addTenToString
def consumer := Proxy.fold (fun acc s => acc ++ s) ""

-- Using forward composition //>
def composed1 := producer //> (fun n => transform n)

-- Using function composition />/
def composed2 := transform />/ (fun s => consumer)

-- Pipeline using push composition >>~
def pushed := producer >>~ transform

end CompositionExample

-- Debugging helpers
namespace Debug

def printEachNumber : Pipe Nat Nat Id Unit :=
  fun ka kb km kp =>
    ka () (fun n =>
      -- In a real implementation, you'd lift IO here
      kb n (fun _ => printEachNumber ka kb km kp))

def countingConsumer : Consumer Nat (StateM Nat) Nat :=
  fun ka _kb km kp =>
    ka () (fun n =>
      km Unit (fun _ =>
        km Nat kp (do
          modify (· + 1)
          get))
        (modify (· + 1)))

-- Test counting
def countTest : Nat :=
  let pipeline := numberProducer >-> countingConsumer
  (Proxy.runEffect pipeline).run 0 |>.2

-- Should return 5 (count of numbers)

end Debug
