

theorem P2_iff_P3_of_open_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen Aᶜ) : P2 A ↔ P3 A := by
  have hClosed : IsClosed (A : Set X) := by
    simpa using h.isClosed_compl
  simpa using (P2_iff_P3_of_closed (A := A) hClosed)

theorem P1_iff_P3_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed Aᶜ) : P1 A ↔ P3 A := by
  have hOpen : IsOpen (A : Set X) := by
    simpa [compl_compl] using h.isOpen_compl
  simpa using (P1_iff_P3_of_open (A := A) hOpen)