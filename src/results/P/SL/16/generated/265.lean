

theorem Topology.isOpen_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- Monotonicity of `interior` yields `interior A ⊆ interior (closure A)`.
  have hSubset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  -- Rewrite with `hInt` to obtain the desired inclusion.
  simpa [hInt] using hSubset