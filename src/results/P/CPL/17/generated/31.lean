

theorem exists_open_between_P1_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  intro _ hP2
  exact
    ⟨interior (closure (interior A)), isOpen_interior, hP2, subset_rfl⟩