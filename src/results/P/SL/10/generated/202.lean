

theorem Topology.interior_closure_inter_interiors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `A ∩ interior B` sits inside `A`, hence its closure sits inside `closure A`.
  have h_closureA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ interior B) ⊆ A)
  -- Likewise, `A ∩ interior B` is contained in `B`, since `interior B ⊆ B`.
  have h_closureB : closure (A ∩ interior B) ⊆ closure B := by
    have h_subset : (A ∩ interior B) ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    exact closure_mono h_subset
  -- Pass to interiors via monotonicity.
  have hxA : x ∈ interior (closure A) := (interior_mono h_closureA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono h_closureB) hx
  exact And.intro hxA hxB