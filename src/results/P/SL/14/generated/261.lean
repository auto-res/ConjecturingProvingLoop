

theorem Topology.clopen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      IsOpen (closure (A : Set X)) ∧ IsClosed (closure (A : Set X)) := by
  intro hDense
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.isOpen_closure_of_dense (X := X) (A := A) hDense
  exact ⟨hOpen, isClosed_closure⟩