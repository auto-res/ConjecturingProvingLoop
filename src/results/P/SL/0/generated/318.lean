

theorem interior_closure_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      ((interior (closure (A : Set X))).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP2
  constructor
  · intro hInt
    exact
      (Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A)) hInt
  · intro hA
    exact
      (Topology.interior_closure_nonempty_of_P2
        (X := X) (A := A)) hP2 hA