

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    simpa using (closure_mono h)
  ·
    have h : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using (closure_mono h)