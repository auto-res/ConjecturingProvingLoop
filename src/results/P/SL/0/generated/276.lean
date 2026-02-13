

theorem union_interiors_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 ((interior (A : Set X)) ∪ interior (B : Set X)) ∧
      Topology.P2 ((interior (A : Set X)) ∪ interior (B : Set X)) ∧
        Topology.P3 ((interior (A : Set X)) ∪ interior (B : Set X)) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Their union is therefore open.
  have hOpen :
      IsOpen ((interior (A : Set X)) ∪ interior (B : Set X) : Set X) :=
    hA.union hB
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X)
      (A := ((interior (A : Set X)) ∪ interior (B : Set X) : Set X))
      hOpen