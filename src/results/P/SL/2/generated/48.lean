

theorem Topology.isClosed_isOpen_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (IsOpen A ↔ Topology.P3 A) := by
  intro hClosed
  constructor
  · intro hOpen
    exact Topology.isOpen_implies_P3 (A := A) hOpen
  · intro hP3
    have hSub : (A : Set X) ⊆ interior A := by
      have : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [hClosed.closure_eq] using this
    have hEq : interior A = A := by
      apply subset_antisymm interior_subset hSub
    exact (isOpen_iff_interior_eq (A := A)).2 hEq