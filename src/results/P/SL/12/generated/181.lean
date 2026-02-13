

theorem Topology.interior_closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B : Set X)) ⊆
      interior (closure (A ∩ B : Set X)) := by
  -- First, observe the basic inclusion `A ∩ interior B ⊆ A ∩ B`.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    have hB : (interior B : Set X) ⊆ B := interior_subset
    exact Set.inter_subset_inter_right _ hB
  -- Apply monotonicity of `closure`.
  have h_closure :
      closure (A ∩ interior B : Set X) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono h_closure