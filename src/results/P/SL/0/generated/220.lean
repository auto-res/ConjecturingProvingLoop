

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the closed–open characterization of `P2`.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X)
      (A := closure (interior (A : Set X)))
      hClosed)