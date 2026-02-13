

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 A → IsOpen A := by
  intro hClosed hP2
  exact open_of_closed_and_P3 hClosed (P3_of_P2 hP2)

theorem exists_clopen_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ IsClosed U ∧ U ⊆ A := by
  intro _
  exact ⟨(∅ : Set X), isOpen_empty, isClosed_empty, Set.empty_subset _⟩