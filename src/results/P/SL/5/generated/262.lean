

theorem interior_closure_nonempty_iff_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact
      Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A) hInt
  · intro hA
    exact
      Topology.interior_closure_nonempty_of_P1
        (X := X) (A := A) hP1 hA