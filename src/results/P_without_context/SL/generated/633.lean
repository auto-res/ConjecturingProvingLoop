

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure
  exact Set.Subset.trans hP2 h_subset