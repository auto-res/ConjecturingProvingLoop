

theorem Topology.nonempty_of_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty → A.Nonempty := by
  rintro ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩