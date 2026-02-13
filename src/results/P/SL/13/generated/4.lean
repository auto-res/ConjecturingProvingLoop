

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure A) :=
    (Topology.isOpen_subset_interiorClosure (X:=X) (A:=A) hA) hx
  simpa [hA.interior_eq] using hx'