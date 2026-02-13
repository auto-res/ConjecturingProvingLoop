

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq, interior_univ] using this

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _
    exact P2_of_open hA