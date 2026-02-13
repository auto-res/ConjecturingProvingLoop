

theorem Topology.interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (A : Set X)) = interior A := by
  simpa [interior_interior]