

theorem P1_exists_closed_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ F, IsClosed F ∧ F ⊆ A ∧ P1 F := by
  intro _
  exact ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, (P1_empty : P1 (∅ : Set X))⟩

theorem P3_union_left_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P3 B → P3 (A ∪ B) := by
  intro hP2A hP3B
  have hP3A : P3 A := P3_of_P2 hP2A
  exact P3_union (A := A) (B := B) hP3A hP3B