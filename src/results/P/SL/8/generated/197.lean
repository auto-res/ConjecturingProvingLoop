

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A \ closure B := by
  intro x hx
  -- Choose an open neighbourhood `U` of `x` contained in `A \ B`.
  rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
  -- `U` is contained in `A`.
  have hU_subA : U ⊆ A := by
    intro y hyU
    have h := hU_sub hyU
    exact h.1
  -- Hence `x ∈ interior A`.
  have hx_intA : x ∈ interior A :=
    (Set.mem_interior).2 ⟨U, hU_open, hU_subA, hxU⟩
  -- Show that `x ∉ closure B` using the open set `U` that avoids `B`.
  have hx_notClB : x ∉ closure B := by
    intro hxClB
    -- Any open set containing `x` must meet `B`, contradicting `U ∩ B = ∅`.
    have hNon : (U ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB U hU_open hxU
    rcases hNon with ⟨y, hyU, hyB⟩
    have hNotB : y ∉ B := by
      have h' := hU_sub hyU
      exact h'.2
    exact hNotB hyB
  -- Assemble the membership in the difference set.
  exact And.intro hx_intA hx_notClB