

theorem Topology.P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  have h₁ := Topology.P1_iff_P2_of_open (A := A) hA
  have h₂ := Topology.P2_iff_P3_of_open (A := A) hA
  exact h₁.trans h₂