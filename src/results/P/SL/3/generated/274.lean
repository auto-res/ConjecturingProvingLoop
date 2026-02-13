

theorem boundary_of_dense_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X))
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (A : Set X) \ A = ((Aᶜ) : Set X) := by
  -- Start with the general description of the boundary of a dense set.
  have h := boundary_of_dense (A := A) hDense
  -- Since `A` is open, `interior A = A`; rewrite both sides accordingly.
  simpa [hOpen.interior_eq] using h