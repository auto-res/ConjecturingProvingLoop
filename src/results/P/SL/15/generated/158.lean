

theorem P1_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P1 B := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_right (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
    have hProd :=
      Topology.P1_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B) hUniv hB
    simpa using hProd