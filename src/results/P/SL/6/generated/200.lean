

theorem P2_implies_P1_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (interior A) := by
  intro hP2
  -- Derive `P1` for `A` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Transfer `P1` from `A` to its interior.
  exact Topology.P1_implies_P1_of_interior (A := A) hP1