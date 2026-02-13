

theorem P3_and_isClosed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P3 A ∧ IsClosed (A : Set X)) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  constructor
  · rintro ⟨hP3, hClosed⟩
    have hOpen : IsOpen (A : Set X) :=
      ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
    exact ⟨hOpen, hClosed⟩
  · rintro ⟨hOpen, hClosed⟩
    have hP3 : Topology.P3 A :=
      ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).2) hOpen
    exact ⟨hP3, hClosed⟩