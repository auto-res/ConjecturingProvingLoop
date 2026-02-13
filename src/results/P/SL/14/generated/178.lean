

theorem Topology.P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closed set.
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  -- Apply the general equivalence between `P2` and openness for closed sets.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (closure A))) h_closed)