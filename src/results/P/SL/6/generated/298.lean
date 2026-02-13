

theorem nonempty_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → A.Nonempty := by
  rintro ⟨x, hxInt⟩
  exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩