

theorem compl_empty {α : Type*} :
    ((∅ : Set α)ᶜ) = (Set.univ : Set α) := by
  ext x
  simp