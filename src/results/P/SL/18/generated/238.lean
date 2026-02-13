

theorem P1_iff_P2_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P1 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we get both `P1` and `P2`.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDenseInt
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (A := A) hDenseInt
  constructor
  · intro _; exact hP2
  · intro _; exact hP1