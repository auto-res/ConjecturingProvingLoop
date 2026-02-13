

theorem Topology.isOpen_implies_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (Topology.P1 (X:=X) A) ∧ (Topology.P2 (X:=X) A) ∧ (Topology.P3 (X:=X) A) := by
  have hP1 := Topology.isOpen_subset_closureInterior (X := X) (A := A) hA
  have hP2 := isOpen_implies_P2 (X := X) (A := A) hA
  have hP3 := Topology.isOpen_subset_interiorClosure (X := X) (A := A) hA
  exact ⟨hP1, hP2, hP3⟩