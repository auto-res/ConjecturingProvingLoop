

theorem closure_interior_nonempty_of_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior (A : Set X)).Nonempty) :
    (closure (interior (A : Set X))).Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩