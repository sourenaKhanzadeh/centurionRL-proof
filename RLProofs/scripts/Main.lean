import RLProofs.Basic

def exampleState := Unit
def exampleAction := Bool

def M : RLSystem exampleState exampleAction := {
  T := fun _ _ => ()  -- Always return unit state
  R := fun _ _ => 1.0 -- Constant reward
  γ := 0.9            -- Discount factor
  π := fun _ => true  -- Always choose true
}

def main : IO Unit := do
  let s := "Hello, world!"
  IO.println s

#eval V M () 10  -- Compute value function for unit state after 10 steps
