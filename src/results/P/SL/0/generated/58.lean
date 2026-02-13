

theorem P2_and_isClosed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P2 A ∧ IsClosed (A : Set X)) ↔ (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · rintro ⟨hP2, hClosed⟩
    have hOpen : IsOpen (A : Set X) :=
      ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP2
    exact ⟨hOpen, hClosed⟩
  · rintro ⟨hOpen, hClosed⟩
    have hP2 : Topology.P2 A :=
      (Topology.isOpen_implies_P2 (X := X) (A := A)) hOpen
    exact ⟨hP2, hClosed⟩