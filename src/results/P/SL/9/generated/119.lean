

theorem Topology.interiorClosure_inter_subset_interiorClosureUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  -- It suffices to use the first component `x ∈ interior (closure A)`;
  -- the argument would be symmetric with `closure B`.
  have hxA : x ∈ interior (closure A) := hx.1
  -- `closure A` is contained in `closure (A ∪ B)`.
  have h_subset : closure A ⊆ closure (A ∪ B) := by
    have hA_union : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact closure_mono hA_union
  -- By monotonicity of `interior`, `x` lies in the desired interior.
  exact (interior_mono h_subset) hxA