

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P1 A := by
  intro x hx
  simpa [h, closure_univ] using (Set.mem_univ x)