

theorem interior_closure_interior_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
    Topology.P2 (interior (closure (interior A))) ∧
    Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hAll :=
    Topology.isOpen_has_all_Ps (X := X) (A := interior (closure (interior A))) hOpen
  simpa using hAll