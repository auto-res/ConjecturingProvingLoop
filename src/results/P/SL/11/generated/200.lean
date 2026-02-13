

theorem Set.nonempty_univ {α : Type*} [Nonempty α] :
    (Set.univ : Set α).Nonempty := by
  classical
  rcases ‹Nonempty α› with ⟨a⟩
  exact ⟨a, by simp⟩