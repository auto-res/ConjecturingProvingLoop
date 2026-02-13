

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is a closed set, so we may apply the general equivalence.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)