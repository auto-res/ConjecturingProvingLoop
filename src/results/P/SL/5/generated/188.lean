

theorem interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  constructor
  · intro hInt
    exact hInt.mono (interior_subset : interior (A : Set X) ⊆ A)
  · intro hA
    exact
      Topology.interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA