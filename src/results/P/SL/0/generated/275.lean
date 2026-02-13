

theorem isOpen_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP3_cl
  have hEquiv := Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).1 hP3_cl