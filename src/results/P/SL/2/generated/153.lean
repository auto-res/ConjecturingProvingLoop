

theorem Topology.isOpen_closure_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hOpenCl
  simpa using
    (Topology.isOpen_implies_P1 (A := closure (A : Set X)) hOpenCl)