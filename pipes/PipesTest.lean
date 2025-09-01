import Std.Internal.Async
open Std.Internal.IO.Async

def log (start : Nat) (tag msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  IO.println s!"[+{elapsed}ms][{tag}] {msg}"

def main : IO Unit := do
  let start ← IO.monoMsNow

  discard $ (do
    log start "Task1" "sleeping 1000ms"
    IO.sleep 1000
    log start "Task1" "woke up"
  ).asTask

  discard $ (do
    for i in [0:6] do
      log start "Task2" s!"tick {i}"
      IO.sleep 200
  ).asTask

  -- Let both tasks finish
  IO.sleep 1500
  let end_ ← IO.monoMsNow
  log start "Main" s!"done after {end_ - start}ms"

-- #eval main
