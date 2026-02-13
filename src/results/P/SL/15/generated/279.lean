

theorem P1_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP1B : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_left_of_nonempty
        (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP1A
    exact
      Topology.P1_prod
        (X := X) (Y := Y) (A := A) (B := B) hP1A hP1B