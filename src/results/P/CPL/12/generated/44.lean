

theorem P3_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 (closure A) := by
  intro h
  intro x hx
  simpa [closure_closure, h, interior_univ] using hx