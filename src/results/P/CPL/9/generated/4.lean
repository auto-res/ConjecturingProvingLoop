

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P3 A := by
  intro x hx
  simpa [hA.closure_eq, interior_univ] using
    (by
      simp : x ∈ (Set.univ : Set X))

theorem P2_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : P2 A := by
  intro x hx
  simp [hA]