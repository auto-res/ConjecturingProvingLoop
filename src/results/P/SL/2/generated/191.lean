

theorem Topology.isClosed_P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP1 hP3
  -- `IsOpen A` follows from the characterisation for closed sets.
  have hOpen : IsOpen A := by
    have hEquiv := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
    exact (hEquiv).mpr ⟨hP1, hP3⟩
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A) hOpen