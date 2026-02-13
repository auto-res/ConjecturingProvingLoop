

theorem Topology.interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior A) = interior A := by
  simpa [interior_interior]