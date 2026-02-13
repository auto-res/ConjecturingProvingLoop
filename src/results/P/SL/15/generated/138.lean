

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  have hP2Univ : Topology.P2 (Set.univ : Set Y) :=
    Topology.P2_univ (X := Y)
  exact
    Topology.P2_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y))
      hP2A hP2Univ