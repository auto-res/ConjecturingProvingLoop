

theorem P2_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P2_prod_univ
        (X := X) (Y := Y) (A := A)) hA