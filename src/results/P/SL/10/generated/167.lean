

theorem Set.Subset_univ {α : Type*} {s : Set α} : s ⊆ (Set.univ : Set α) := by
  intro x _
  simp