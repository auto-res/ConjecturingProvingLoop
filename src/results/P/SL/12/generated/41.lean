

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP3
    -- `A ⊆ interior (closure A)` and `closure A = A` yield `A ⊆ interior A`.
    have h_sub : (A : Set X) ⊆ interior A := by
      dsimp [Topology.P3] at hP3
      simpa [h_closed.closure_eq] using hP3
    -- Together with `interior A ⊆ A` we get equality.
    have h_eq : interior (A : Set X) = A :=
      Set.Subset.antisymm interior_subset h_sub
    -- An equality with an open set yields openness of `A`.
    have h_open : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_eq] using this
    exact h_open
  · intro h_open
    exact Topology.isOpen_P3 (X := X) (A := A) h_open