

theorem union_three_interiors_has_all_Ps {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    Topology.P1
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) ∧
      Topology.P2
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) ∧
        Topology.P3
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X)) := by
  -- The union of three open sets is open.
  have hOpen :
      IsOpen
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X) : Set X) := by
    have hAB :
        IsOpen
          ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) :=
      (isOpen_interior).union isOpen_interior
    simpa [Set.union_assoc] using hAB.union isOpen_interior
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X)
      (A :=
        ((interior (A : Set X)) ∪ interior (B : Set X) ∪ interior (C : Set X) : Set X))
      hOpen