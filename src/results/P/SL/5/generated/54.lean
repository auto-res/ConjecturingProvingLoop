

theorem P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- Since `A` is closed, its closure is itself.
    have h_closure_eq : closure (A : Set X) = A := hA_closed.closure_eq
    -- `P3` provides `A ⊆ interior (closure A) = interior A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h_closure_eq] using hx'
    -- Combine with `interior_subset` to get the equality `interior A = A`.
    have h_eq : interior (A : Set X) = A := by
      apply le_antisymm
      · exact interior_subset
      · exact h_subset
    -- Use the fact that `interior A` is open and rewrite with the equality.
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h_eq] using this
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen