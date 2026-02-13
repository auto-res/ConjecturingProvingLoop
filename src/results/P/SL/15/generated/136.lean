

theorem P1_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ (Topology.P1 A ∧ Topology.P1 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_implies_P1_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP1A, hP1B⟩
    exact
      Topology.P1_prod (X := X) (Y := Y) (A := A) (B := B) hP1A hP1B