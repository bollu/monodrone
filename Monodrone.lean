
structure Context where
  x : Int

@[export monodrone_new_context]
def newContext (x : Unit): Context := { x := 0 }
