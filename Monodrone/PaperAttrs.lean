import Lean.Elab.Tactic.Config

open Lean Meta

initialize coolSimpExtension : SimpExtension ←
  registerSimpAttr `cool
    "a simp lemma that tags definitions that are cool for the paper."
