

theorem P2_iff_P1_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (A : Set X) ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2
  · intro hP1
    dsimp [Topology.P2] at *
    simpa [hOpen.interior_eq] using hP1