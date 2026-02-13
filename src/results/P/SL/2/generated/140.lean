

theorem Topology.isClosed_isOpen_implies_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → IsOpen A → closure (interior A) = A := by
  intro hClosed hOpen
  simpa [hOpen.interior_eq, hClosed.closure_eq]