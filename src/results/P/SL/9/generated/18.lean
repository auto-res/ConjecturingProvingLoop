

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  have h1 := (Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed)
  have h2 := (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed)
  exact h1.trans h2.symm