

theorem isOpen_closure_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2_cl
  have hEquiv :=
    Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).1 hP2_cl