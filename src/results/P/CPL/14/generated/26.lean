

theorem P1_interior_of_P3 {X} [TopologicalSpace X] {A : Set X} : P3 A → P1 (interior A) := by
  intro _hP3
  intro x hx
  simpa [interior_interior] using (subset_closure hx)