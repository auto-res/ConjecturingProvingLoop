

theorem isOpen_closure_iff_P2_and_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      (Topology.P2 (closure (A : Set X)) ∧ Topology.P3 (closure (A : Set X))) := by
  constructor
  · intro hOpen
    have hP2 : Topology.P2 (closure (A : Set X)) :=
      (Topology.isOpen_implies_P2 (X := X) (A := closure (A : Set X))) hOpen
    have hP3 : Topology.P3 (closure (A : Set X)) :=
      (Topology.isOpen_implies_P3 (X := X) (A := closure (A : Set X))) hOpen
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    have hEquiv :=
      Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2