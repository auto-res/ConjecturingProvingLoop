

theorem nonempty_of_interior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, interior_subset hxInt⟩