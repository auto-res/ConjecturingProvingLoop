

theorem Topology.P3_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (A : Set X)) →
      Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP3cl
  -- From `P3` we infer that `closure A` is open, using the established equivalence.
  have h_open : IsOpen (closure (A : Set X)) :=
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1) hP3cl
  -- Every open set satisfies `P1`.
  simpa using
    (Topology.isOpen_subset_closureInterior
      (X := X) (A := closure (A : Set X)) h_open)