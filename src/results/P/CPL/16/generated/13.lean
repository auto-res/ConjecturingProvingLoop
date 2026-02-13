

theorem exists_P1_closed_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ IsClosed B ∧ P1 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isClosed_empty, P1_empty⟩

theorem exists_P2_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsOpen B ∧ P2 B := by
  refine ⟨Set.univ, ?_, isOpen_univ, P2_univ⟩
  intro x hx
  trivial