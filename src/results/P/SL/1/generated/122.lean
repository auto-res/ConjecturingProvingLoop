

theorem Topology.interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) :
    interior (closure A) = (Set.univ : Set X) := by
  have hclosure : closure A = (Set.univ : Set X) := by
    simpa using h.closure_eq
  simpa [hclosure, interior_univ]