

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _
  exact P3_of_open (A := interior A) isOpen_interior