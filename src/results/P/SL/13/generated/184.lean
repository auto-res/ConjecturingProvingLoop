

theorem Topology.dense_of_P2_and_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hDenseInt : Dense (interior (A : Set X))) :
    Dense (A : Set X) := by
  -- From `P2` we get `P1`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  -- Use the existing lemma that combines `P1` with density of `interior A`.
  exact
    Topology.dense_of_P1_and_denseInterior
      (X := X) (A := A) hP1 hDenseInt