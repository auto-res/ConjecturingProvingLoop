

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P2 A := by
  intro hIntUniv
  intro x _
  simpa [hIntUniv, closure_univ, interior_univ] using (Set.mem_univ x)