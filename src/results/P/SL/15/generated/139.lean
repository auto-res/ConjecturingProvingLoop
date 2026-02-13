

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P1 (Set.univ : Set Y) :=
    Topology.P1_univ (X := Y)
  exact
    Topology.P1_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv