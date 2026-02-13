

theorem Topology.P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closed set.
  have hClosed : IsClosed (closure (interior (closure A))) := isClosed_closure
  -- Apply the existing equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (closure A))) hClosed)