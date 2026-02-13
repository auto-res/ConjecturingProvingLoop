

theorem P3_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ (Topology.P3 A ∧ Topology.P3 B) := by
  constructor
  · intro hP3Prod
    have hP3A : Topology.P3 A :=
      Topology.P3_of_P3_prod_left (A := A) (B := B) hB hP3Prod
    have hP3B : Topology.P3 B :=
      Topology.P3_of_P3_prod_right (A := A) (B := B) hA hP3Prod
    exact ⟨hP3A, hP3B⟩
  · rintro ⟨hP3A, hP3B⟩
    exact Topology.P3_prod hP3A hP3B