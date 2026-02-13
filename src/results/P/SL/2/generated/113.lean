

theorem Topology.isClosed_isOpen_iff_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (IsOpen A ↔ (Topology.P1 A ∧ Topology.P2 A)) := by
  intro hClosed
  have h₁ : IsOpen A ↔ Topology.P2 A :=
    (Topology.isClosed_P2_iff_isOpen (A := A) hClosed).symm
  constructor
  · intro hOpen
    have hP2 : Topology.P2 A := (h₁).1 hOpen
    have hP1 : Topology.P1 A := Topology.isOpen_implies_P1 (A := A) hOpen
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    exact (Topology.isClosed_P2_implies_isOpen (A := A)) hClosed hP2