

theorem Topology.P3_closureInterior_iff_isOpen_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always a closed set.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the generic equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) h_closed)