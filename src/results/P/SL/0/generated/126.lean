

theorem P3_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hOpen
  have hEquiv := Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact (hEquiv).2 hOpen