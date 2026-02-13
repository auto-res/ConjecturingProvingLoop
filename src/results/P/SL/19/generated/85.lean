

theorem Topology.closure_interior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP3
  apply Set.Subset.antisymm
  · exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    exact closure_mono hSub