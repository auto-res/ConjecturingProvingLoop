

theorem Topology.P2_closureInterior_iff_isOpen_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always closed.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) h_closed)