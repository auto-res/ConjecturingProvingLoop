

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  simpa using compl_compl (s := s)