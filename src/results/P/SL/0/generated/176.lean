

theorem isOpen_union_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen ((interior (A : Set X)) ∪ interior (B : Set X)) := by
  -- Both `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  have hB : IsOpen (interior (B : Set X)) := isOpen_interior
  -- The union of two open sets is open.
  exact hA.union hB