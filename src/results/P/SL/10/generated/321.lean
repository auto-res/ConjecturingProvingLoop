

theorem Topology.interior_inter_closure_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A ∩ closure B := by
  intro x hx
  -- `hx` places `x` inside the interior of `A ∩ closure B`.
  have h_mem : x ∈ A ∩ closure B := interior_subset hx
  have hxClB : x ∈ closure B := h_mem.2
  -- Monotonicity of `interior` shows that `x` also lies in `interior A`.
  have hxIntA : x ∈ interior A := by
    have h_subset : interior (A ∩ closure B) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ closure B) ⊆ A)
    exact h_subset hx
  exact And.intro hxIntA hxClB