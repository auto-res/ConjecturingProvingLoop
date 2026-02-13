

theorem Topology.interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    -- Since `interior A ⊆ A` and `A` is closed, we have
    -- `closure (interior A) ⊆ A`.
    have hSub : closure (interior A) ⊆ A := by
      have hInt : (interior A : Set X) ⊆ A := interior_subset
      have hClos : closure (interior A) ⊆ closure A := closure_mono hInt
      simpa [hA.closure_eq] using hClos
    -- Monotonicity of `interior` gives the desired inclusion.
    exact (interior_mono hSub) hx
  · intro x hx
    -- Use the maximality of the interior: if `interior A` is contained in a set,
    -- then its interior contains `interior A`.
    have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have hInc : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal hSub isOpen_interior
    exact hInc hx