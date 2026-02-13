

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A → Topology.P3 A := by
    intro _hP1
    exact Topology.open_satisfies_P3 (A := A) hA
  have h₂ : Topology.P3 A → Topology.P1 A := by
    intro hP3
    have hP2 : Topology.P2 A :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).1 hP3
    exact Topology.P2_implies_P1 (A := A) hP2
  exact ⟨h₁, h₂⟩