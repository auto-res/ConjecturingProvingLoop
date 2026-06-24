

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  dsimp [P2, P3]
  intro hP2
  apply subset_trans hP2
  exact interior_mono (closure_mono (interior_subset : interior A ⊆ A))

theorem dense_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply le_antisymm
  · exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h

theorem interior_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → interior A ⊆ interior (closure A) := by
  dsimp [P3]
  intro hP3
  exact subset_trans (interior_subset : interior A ⊆ A) hP3

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro h_dense
  dsimp [P3]
  simpa [h_dense, interior_univ] using (subset_univ A)