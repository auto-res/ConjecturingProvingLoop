

theorem Topology.closure_interior_diff_subset_closure_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) \ interior B := by
  classical
  intro x hx
  -- First, `x` lies in `closure (interior A)` because
  -- `interior (A \ B) ⊆ interior A`.
  have hx_closureA : x ∈ closure (interior A) := by
    have h_subset : interior (A \ B) ⊆ interior A :=
      Topology.interior_diff_subset_interior_left (A := A) (B := B)
    exact (closure_mono h_subset) hx
  -- Next, we show `x ∉ interior B`; otherwise we obtain a contradiction.
  have hx_not_intB : x ∉ interior B := by
    intro hxIntB
    -- The open set `interior B` contains `x`.
    have h_nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases h_nonempty with ⟨y, hyIntB, hyIntDiff⟩
    -- From `y ∈ interior (A \ B)` we know `y ∈ A \ B`, so `y ∉ B`.
    have hy_notB : y ∉ B := (interior_subset hyIntDiff).2
    -- But `y ∈ interior B` implies `y ∈ B`, contradiction.
    exact hy_notB (interior_subset hyIntB)
  -- Assemble the required membership in the set difference.
  exact And.intro hx_closureA hx_not_intB