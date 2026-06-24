

theorem Topology.P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    dsimp [Topology.P1]
    have h : A ⊆ interior (closure (interior A)) := by
      simpa [Topology.P2] using hP2
    exact Set.Subset.trans h interior_subset
  have hP3 : Topology.P3 A := by
    dsimp [Topology.P3]
    have h : A ⊆ interior (closure (interior A)) := by
      simpa [Topology.P2] using hP2
    have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
      have h_closure_subset : closure (interior A) ⊆ closure A :=
        closure_mono interior_subset
      exact interior_mono h_closure_subset
    exact Set.Subset.trans h h_subset
  exact And.intro hP1 hP3