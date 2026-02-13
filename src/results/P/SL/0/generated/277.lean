

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A →
      ((interior (A : Set X)).Nonempty ↔ (A : Set X).Nonempty) := by
  intro hP1
  constructor
  · intro hInt
    exact hInt.mono (interior_subset : interior (A : Set X) ⊆ A)
  · intro hA
    exact
      (Topology.interior_nonempty_of_P1 (X := X) (A := A)) hP1 hA