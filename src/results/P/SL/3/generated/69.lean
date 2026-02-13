

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    IsOpen (A : Set X) := by
  -- From `P3` and the fact that `A` is closed, we have `A ⊆ interior A`.
  have h_subset : (A : Set X) ⊆ interior (A : Set X) := by
    have hP3' : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa [hA_closed.closure_eq] using hP3'
  -- Hence `interior A = A`.
  have h_eq : interior (A : Set X) = A := by
    apply Set.Subset.antisymm
    · exact interior_subset (s := A)
    · exact h_subset
  -- `interior A` is open, so `A` is open as well.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this