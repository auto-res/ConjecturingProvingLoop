

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior A = interior A := by
  have h := Topology.interior_inter_closure_eq_interior (X := X) (A := A)
  simpa [Set.inter_comm] using h.symm