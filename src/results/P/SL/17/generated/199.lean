

theorem Topology.interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    interior (closure A) = A := by
  classical
  -- First, prove `closure A = A`.
  have h_closure_eq : closure A = A := by
    apply Set.Subset.antisymm
    · intro x hx_cl
      by_cases hxA : x ∈ A
      · exact hxA
      ·
        -- The singleton `{x}` is open in a discrete space.
        have h_open : IsOpen ({x} : Set X) := isOpen_discrete _
        -- Since `{x}` contains `x` and is open, density in the closure forces
        -- a contradiction if `x ∉ A`.
        have h_nonempty :
            (({x} : Set X) ∩ A).Nonempty :=
          (mem_closure_iff).1 hx_cl ({x}) h_open (by
            simp)
        rcases h_nonempty with ⟨y, ⟨hy_single, hyA⟩⟩
        have h_eq : y = x := by
          simpa [Set.mem_singleton_iff] using hy_single
        have : x ∈ A := by
          simpa [h_eq] using hyA
        exact this
    · exact subset_closure
  -- In a discrete space every set is open, so `interior A = A`.
  have h_interior_eq : interior A = A :=
    (isOpen_discrete _).interior_eq
  -- Rewrite using the two equalities obtained above.
  simpa [h_closure_eq, h_interior_eq]