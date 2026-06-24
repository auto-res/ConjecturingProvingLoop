

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  have h_mono : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h_int_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_mono
  exact subset_trans hP2 h_int_mono