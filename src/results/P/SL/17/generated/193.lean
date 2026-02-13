

theorem Topology.closure_interior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    closure (interior A) = A := by
  -- In a discrete topology every set is open, in particular `A`.
  have hOpen : IsOpen A := isOpen_discrete _
  -- Hence `interior A = A`.
  have hInt : interior A = A := hOpen.interior_eq
  -- It suffices to show `closure A = A`.
  suffices closure A = A by
    simpa [hInt] using this
  -- Prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- Show `closure A ⊆ A`.
    intro x hx
    -- The singleton `{x}` is open in a discrete space.
    have hOpenSingleton : IsOpen ({x} : Set X) := isOpen_discrete _
    -- By definition of the closure, `{x}` meets `A`.
    have hNonempty :
        (({x} : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx ({x}) hOpenSingleton (by
        -- `x` belongs to the open set `{x}`.
        simp)
    -- Extract a witness from the non-empty intersection.
    rcases hNonempty with ⟨y, ⟨hySingle, hyA⟩⟩
    -- From `y ∈ {x}` we deduce `y = x`.
    have : y = x := by
      simpa [Set.mem_singleton_iff] using hySingle
    -- Conclude `x ∈ A`.
    simpa [this] using hyA
  · -- The reverse inclusion is always true.
    exact subset_closure