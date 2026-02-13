

theorem P2_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (interior (A : Set X))) := by
  simpa using
    (P2_interior (X := X) (A := interior (A : Set X)))