

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA x hx
  simpa [hA.interior_eq] using (subset_closure hx : x ∈ closure A)

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense x hx
  simpa [hDense, interior_univ] using (Set.mem_univ x)