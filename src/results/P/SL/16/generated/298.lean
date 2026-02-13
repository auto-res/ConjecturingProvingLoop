

theorem Topology.interior_closure_inter_subset_inter_interior_closure_leftInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Left component: `x ∈ interior (closure A)`
  have hx_left : x ∈ interior (closure A) := by
    -- Since `A ∩ interior B ⊆ A`, taking closures yields the desired inclusion.
    have h_cl_sub : closure (A ∩ interior B) ⊆ closure A := by
      apply closure_mono
      intro y hy
      exact hy.1
    exact (interior_mono h_cl_sub) hx
  -- Right component: `x ∈ interior (closure B)`
  have hx_right : x ∈ interior (closure B) := by
    -- Use `interior B ⊆ B` to show `A ∩ interior B ⊆ B`.
    have h_cl_sub : closure (A ∩ interior B) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact
        (interior_subset : interior B ⊆ B) hy.2
    exact (interior_mono h_cl_sub) hx
  exact And.intro hx_left hx_right