

theorem P2_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P2_closed_iff_isOpen (A := closure (interior A)) hClosed)