

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
        (A := closure (interior A)) hClosed)