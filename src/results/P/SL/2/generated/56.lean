

theorem Topology.isClosed_P3_iff_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → (Topology.P3 A ↔ interior A = A) := by
  intro hClosed
  have h₁ := (Topology.isClosed_isOpen_iff_P3 (A := A) hClosed)
  have h₂ := (isOpen_iff_interior_eq (A := A))
  simpa using (h₁.symm.trans h₂)