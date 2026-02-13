

theorem Topology.P2_closureInteriorClosure_iff_P3_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      Topology.P3 (closure (interior (closure A))) := by
  -- Both properties are equivalent to the set being open.
  have h₁ :=
    Topology.P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
      (X := X) (A := A)
  have h₂ :=
    Topology.P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
      (X := X) (A := A)
  -- Chain the equivalences.
  exact h₁.trans h₂.symm