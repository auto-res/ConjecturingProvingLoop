

theorem P2_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hOpen
  have h := (P2_closure_iff_isOpen_closure (A := A)).mpr hOpen
  simpa using h