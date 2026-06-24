

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_cl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono h_cl
  exact Set.Subset.trans hP2 h_sub