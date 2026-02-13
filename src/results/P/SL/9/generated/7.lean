

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (A := A) ↔ IsOpen A := by
  dsimp [Topology.P3] at *
  have h_closure_eq : closure A = A := hA_closed.closure_eq
  constructor
  · intro hP3
    -- Rewrite using the fact that `closure A = A`.
    have h_subset : A ⊆ interior A := by
      simpa [h_closure_eq] using hP3
    -- `interior A` is always a subset of `A`.
    have h_subset' : interior A ⊆ A := interior_subset
    -- Hence `interior A = A`.
    have h_eq : interior A = A := subset_antisymm h_subset' h_subset
    -- An interior is open, and equality gives the desired openness of `A`.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    -- Since `A` is open, it is contained in its own interior.
    have h1 : A ⊆ interior A := by
      simpa [hA_open.interior_eq] using (subset_rfl : A ⊆ A)
    -- The interior is monotone with respect to set inclusion.
    have h2 : interior A ⊆ interior (closure A) :=
      interior_mono subset_closure
    -- Combining the two inclusions yields the desired result.
    exact subset_trans h1 h2