

theorem P2_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP2B : Topology.P2 B) :
    Topology.P2 (A ×ˢ B) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_left_of_nonempty
          (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP2A
    exact
      Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hP2A hP2B