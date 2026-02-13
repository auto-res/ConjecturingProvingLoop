

theorem Topology.interior_closure_interior_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior A))) ∧
    Topology.P2 (X := X) (interior (closure (interior A))) ∧
    Topology.P3 (X := X) (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hP1 : Topology.P1 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P1 (X := X) (A := interior (closure (interior A))) hOpen
  have hP2 : Topology.P2 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) hOpen
  have hP3 : Topology.P3 (X := X) (interior (closure (interior A))) :=
    Topology.isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) hOpen
  exact ⟨hP1, hP2, hP3⟩