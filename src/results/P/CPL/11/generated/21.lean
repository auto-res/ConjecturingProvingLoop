

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := by
  exact (P2_iff_P1_P3).2 ⟨h1, h3⟩

theorem exists_closed_superset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ C, IsClosed C ∧ A ⊆ C := by
  simpa using exists_closed_superset_of_P1 (A := A) (hA := P1_of_P2 hA)