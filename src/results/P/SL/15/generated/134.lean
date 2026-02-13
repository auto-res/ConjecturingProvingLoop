

theorem P3_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ (Topology.P3 A ∧ Topology.P3 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_implies_P3_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP3A, hP3B⟩
    exact
      Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B