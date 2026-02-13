

theorem Topology.isClosed_isOpen_iff_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A →
      (IsOpen A ↔ (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A)) := by
  intro hClosed
  have h₁ := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
  have h₂ := (Topology.isClosed_P2_iff_isOpen (A := A) hClosed)
  constructor
  · intro hOpen
    have hP1P3 : Topology.P1 A ∧ Topology.P3 A := (h₁).1 hOpen
    have hP2 : Topology.P2 A := (h₂).2 hOpen
    exact ⟨hP1P3.1, hP2, hP1P3.2⟩
  · rintro ⟨_, hP2, _⟩
    exact (h₂).1 hP2