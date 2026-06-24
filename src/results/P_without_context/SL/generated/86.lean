

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  have h_int_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hP2 h_int_subset