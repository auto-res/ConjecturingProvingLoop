

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- `P2` holds for every open set.
  have hP2_open : Topology.P2 A := by
    dsimp [Topology.P2]
    have hsubset : (A : Set X) ⊆ interior (closure A) := by
      have hcl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_maximal hcl hA
    simpa [hA.interior_eq] using hsubset
  -- Construct the equivalence.
  constructor
  · intro _
    exact hP2_open
  · intro hP2
    exact (Topology.P2_implies_P1 (X := X) (A := A)) hP2