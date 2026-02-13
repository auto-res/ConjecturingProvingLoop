

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hAopen
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hAopen.interior_eq] using hx
  exact subset_closure hx_int