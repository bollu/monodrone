import Lean
import Monodrone
open Lean


def test1 : IO Unit := do
  IO.println "lower semitone"
  let ctx : RawContext := newContext ()
  let ctx := ctx.lowerSemitone
  IO.println s!"done. ctx: {repr ctx}"

def main : IO Unit := do
  test1
