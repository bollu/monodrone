import Lean.Elab.Tactic.Config

open Lean Meta

initialize noteOmegaSimpExtension : SimpExtension ←
  registerSimpAttr `note_omega
    "simp lemmas converting `Note` goals to `Nat` goals, for use with `omega`"
