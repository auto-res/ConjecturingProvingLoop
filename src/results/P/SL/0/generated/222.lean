

theorem isOpen_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    IsOpen (A ∪ interior (B : Set X)) := by
  have hIntB : IsOpen (interior (B : Set X)) := isOpen_interior
  exact hA.union hIntB