

theorem P2_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ (Topology.P2 A ∧ Topology.P2 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_implies_P2_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP2A, hP2B⟩
    exact
      Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hP2A hP2B