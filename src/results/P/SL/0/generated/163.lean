

theorem isOpen_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    IsOpen ((interior (A : Set X)) ∪ B) := by
  have hA : IsOpen (interior (A : Set X)) := isOpen_interior
  exact hA.union hB