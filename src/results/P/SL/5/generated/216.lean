

theorem isOpen_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ Topology.P3 (X := X) (closure (A : Set X)) := by
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Use the existing equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X)
      (A := closure (A : Set X)) hClosed).symm