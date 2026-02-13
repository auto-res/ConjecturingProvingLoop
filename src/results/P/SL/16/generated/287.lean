

theorem Set.nonempty_univ {α : Type*} [h : Nonempty α] :
    (Set.univ : Set α).Nonempty := by
  classical
  rcases h with ⟨x⟩
  exact ⟨x, by simp⟩