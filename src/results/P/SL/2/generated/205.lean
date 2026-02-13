

theorem Topology.isOpen_closure_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hOpenCl
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.isClosed_isOpen_implies_closure_interior_eq_self
        (A := closure (A : Set X)) hClosed hOpenCl)