

theorem Set.compl_compl {α : Type*} (s : Set α) : (sᶜᶜ : Set α) = s := by
  ext x
  by_cases h : x ∈ s <;> simp [h]