

theorem closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (closure (interior (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hCl
    exact
      Topology.nonempty_of_closure_interior_nonempty
        (X := X) (A := A) hCl
  · intro hA
    exact
      Topology.closure_interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA