

theorem Topology.P1_iff_empty_of_emptyInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior (A : Set X) = (∅ : Set X)) :
    Topology.P1 (X := X) A ↔ (A : Set X) = (∅ : Set X) := by
  constructor
  · intro hP1
    exact
      Topology.P1_and_emptyInterior_implies_empty (X := X) (A := A) hP1 h_int
  · intro hA
    simpa [hA] using Topology.P1_empty (X := X)