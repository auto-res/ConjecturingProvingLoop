

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h, interior_univ] using this