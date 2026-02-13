

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hxInt
  -- From `hxInt : x ∈ interior (A \ B)`, we know `x ∈ A \ B`.
  have hxDiff : x ∈ A \ B := interior_subset hxInt
  -- Hence `x ∈ A`.
  have hxA : x ∈ A := hxDiff.1
  -- We claim that `x ∉ closure B`.
  have hxNotClB : x ∉ closure B := by
    intro hxClB
    -- Use the neighbourhood characterisation of closure.
    have h_cl := (mem_closure_iff).1 hxClB
    -- The open neighbourhood `interior (A \ B)` of `x` is disjoint from `B`,
    -- contradicting the definition of closure.
    have h_nonempty : ((interior (A \ B : Set X)) ∩ B).Nonempty := by
      have h_open : IsOpen (interior (A \ B : Set X)) := isOpen_interior
      exact h_cl _ h_open hxInt
    rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    have hyDiff : y ∈ A \ B := interior_subset hyInt
    exact (hyDiff.2 hyB).elim
  exact ⟨hxA, hxNotClB⟩