@[inline, specialize]
def Array.partitionMapM [Monad m] (f : α → m (β ⊕ γ)) (as : Array α) : m (Array β × Array γ) := do
  let mut bs := #[]
  let mut cs := #[]
  for a in as do
    match ← f a with
    | Sum.inl b => bs := bs.push b
    | Sum.inr c => cs := cs.push c
  return (bs, cs)
