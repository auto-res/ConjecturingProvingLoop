

theorem Set.compl_compl {α : Type*} {s : Set α} : ((sᶜ)ᶜ : Set α) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]