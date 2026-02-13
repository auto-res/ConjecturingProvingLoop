

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  have hP1_univ : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)

theorem P2_has_closed_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ C : Set X, IsClosed C ∧ C ⊆ A ∧ P2 C := by
  intro _
  exact
    ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P2_empty (X := X)⟩