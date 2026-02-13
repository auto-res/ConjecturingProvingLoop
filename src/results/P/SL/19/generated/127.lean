

theorem Topology.closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) → closure A ⊆ closure (interior A) := by
  intro hP1
  exact (Topology.P1_iff_closure_subset_closure_interior (X := X) (A := A)).1 hP1