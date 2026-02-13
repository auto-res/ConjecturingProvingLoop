

theorem Topology.closureInterior_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior A = interior A := by
  simpa [interior_interior] using
    (Topology.closure_inter_interior_eq_interior (A := interior A))