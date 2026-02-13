

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → (Topology.P3 A ↔ IsOpen A) := by
  intro hClosed
  have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
  constructor
  · intro hP3
    -- First, show `A ⊆ interior A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h_closure_eq] using hx'
    -- Hence `interior A = A`.
    have h_int_eq : interior (A : Set X) = A := by
      apply le_antisymm
      · exact interior_subset
      · exact h_subset
    -- Therefore `A` is open.
    have hIsOpen : IsOpen A := by
      simpa [h_int_eq] using
        (isOpen_interior : IsOpen (interior (A : Set X)))
    exact hIsOpen
  · intro hOpen
    exact P3_of_open (A := A) hOpen