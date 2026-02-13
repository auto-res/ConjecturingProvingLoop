

theorem interior_closure_nonempty_iff_nonempty_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      ((interior (closure (A : Set X))).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP3
  constructor
  · intro hInt
    exact
      (Topology.nonempty_of_interior_closure_nonempty
        (X := X) (A := A)) hInt
  · intro hA
    exact
      (Topology.interior_closure_nonempty_of_P3
        (X := X) (A := A)) hP3 hA