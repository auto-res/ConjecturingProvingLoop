

theorem Topology.P2_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔
      IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is a closed set.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the closed‐set characterization of `P2`.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)