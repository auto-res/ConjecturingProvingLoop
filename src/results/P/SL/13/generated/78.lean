

theorem Topology.isOpen_closure_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen (closure (A : Set X))) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- Apply the generic P1 result for open sets to `closure A`.
  have hP1 :=
    isOpen_subset_closureInterior (X := X) (A := closure (A : Set X)) h_open
  simpa using hP1