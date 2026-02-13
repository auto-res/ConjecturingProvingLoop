

theorem Topology.P1_iff_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _
    dsimp [Topology.P2]
    have h_subset : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    simpa [hA.interior_eq] using h_subset
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2