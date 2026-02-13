

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ (X := Y)
  exact
    Topology.P3_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv