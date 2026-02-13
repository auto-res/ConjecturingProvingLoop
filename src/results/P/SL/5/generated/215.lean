

theorem closure_interior_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    (closure (interior (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · exact Topology.nonempty_of_closure_interior_nonempty (X := X) (A := A)
  · exact Topology.closure_interior_nonempty_of_P1 (X := X) (A := A) hP1