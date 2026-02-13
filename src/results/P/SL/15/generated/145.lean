

theorem P1_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P1_prod_univ
        (X := X) (Y := Y) (A := A)) hA