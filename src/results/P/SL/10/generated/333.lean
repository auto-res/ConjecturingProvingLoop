

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ A \ closure B := by
  intro x hxInt
  -- From `hxInt` we know that `x ∈ A \ B`.
  have hxAB : x ∈ A ∧ x ∉ B := by
    have : x ∈ (A \ B) := interior_subset hxInt
    exact this
  have hxA : x ∈ A := hxAB.1
  -- We now show `x ∉ closure B`; otherwise we obtain a contradiction.
  have hxNotClB : x ∉ closure B := by
    intro hxClB
    -- Because `x ∈ interior (A \ B)`, the set `interior (A \ B)` is an open
    -- neighbourhood of `x` disjoint from `B`.
    have h_nonempty :=
      (mem_closure_iff).1 hxClB (interior (A \ B)) isOpen_interior hxInt
    rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    -- But `hyInt : y ∈ interior (A \ B)` implies `y ∉ B`, contradicting `hyB`.
    have : y ∉ B := (interior_subset hyInt).2
    exact this hyB
  exact And.intro hxA hxNotClB