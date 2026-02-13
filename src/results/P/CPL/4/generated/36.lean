

theorem P1_exists_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ F : Set X, IsClosed F ∧ A ⊆ F ∧ F ⊆ closure (interior A) := by
  intro hP1
  exact ⟨closure (interior A), isClosed_closure, hP1, subset_rfl⟩