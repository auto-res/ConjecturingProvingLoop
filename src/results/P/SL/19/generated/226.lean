

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ A \ closure B := by
  intro x hxInt
  -- `x` lies in `A \ B`.
  have hAB : x ∈ A \ B := interior_subset hxInt
  have hA : x ∈ A := hAB.1
  -- We show `x ∉ closure B`.
  have hNotClB : x ∉ closure B := by
    intro hxClB
    -- The open neighbourhood `U := interior (A \ B)` of `x`
    -- must intersect `B` because `x ∈ closure B`.
    have hNon :
        ((interior (A \ B) : Set X) ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB (interior (A \ B)) isOpen_interior hxInt
    rcases hNon with ⟨y, ⟨hyInt, hyB⟩⟩
    -- But `y ∈ interior (A \ B)` implies `y ∉ B`, contradiction.
    have hNotB : y ∉ B := (interior_subset hyInt).2
    exact hNotB hyB
  exact And.intro hA hNotClB