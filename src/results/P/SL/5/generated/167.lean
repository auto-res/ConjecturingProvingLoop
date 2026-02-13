

theorem interior_diff_subset_interior_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A \ closure B := by
  intro x hx
  rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
  -- `x` belongs to the interior of `A`
  have hUsubA : (U : Set X) ⊆ A := by
    intro y hy
    exact (hUsub hy).1
  have hx_intA : x ∈ interior A :=
    mem_interior.2 ⟨U, hUsubA, hUopen, hxU⟩
  -- `x` does not belong to the closure of `B`
  have hx_notClB : x ∉ closure B := by
    intro hxClB
    -- Using the neighbourhood `U`, derive a contradiction with `U ⊆ A \ B`
    have hNon : ((U : Set X) ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyB⟩⟩
    have : y ∉ B := (hUsub hyU).2
    exact this hyB
  exact ⟨hx_intA, hx_notClB⟩