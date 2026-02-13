

theorem P1_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) : P1 A := by
  intro x hxA
  simpa [h] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  simpa using (P3_of_P2 (P2_of_open hA))

theorem P3_of_dense {X} [TopologicalSpace X] {A : Set X} (h : closure A = (Set.univ : Set X)) : P3 A := by
  intro x hxA
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hInt]