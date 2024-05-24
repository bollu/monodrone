
structure Context where
  x : Int

@[export new_context]
def newContext (x : Unit): Context := {}
