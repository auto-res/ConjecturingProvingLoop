

theorem P3_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP3B : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_left_of_nonempty
        (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP3A
    exact
      Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B