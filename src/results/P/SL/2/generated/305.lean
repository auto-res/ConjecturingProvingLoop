

theorem Topology.interior_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  exact Topology.interior_closure_subset_closure_interior_of_P1 (A := A) hP1