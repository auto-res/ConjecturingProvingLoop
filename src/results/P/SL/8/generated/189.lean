

theorem interior_nonempty_imp_nonempty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior A).Nonempty) : A.Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩