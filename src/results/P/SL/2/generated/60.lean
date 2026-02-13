

theorem Topology.isClosed_P3_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → IsOpen A := by
  intro hClosed hP3
  have hIntEq : interior A = A := by
    have h := Topology.isClosed_P3_implies_interior_closure_eq_self (A := A) hClosed hP3
    simpa [hClosed.closure_eq] using h
  have : IsOpen (interior A) := isOpen_interior
  simpa [hIntEq] using this