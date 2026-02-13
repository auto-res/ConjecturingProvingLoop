

theorem subset_univ {α : Type*} {s : Set α} : s ⊆ (Set.univ : Set α) := by
  intro x hx
  trivial