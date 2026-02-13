

theorem Topology.interior_closure_inter_closures_subset_inter_interior_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in `closure A`.
  have h_subsetA :
      (closure (A : Set X) ∩ closure B : Set X) ⊆ closure A :=
    Set.inter_subset_left
  -- `closure A ∩ closure B` is also contained in `closure B`.
  have h_subsetB :
      (closure (A : Set X) ∩ closure B : Set X) ⊆ closure B :=
    Set.inter_subset_right
  -- Apply the monotonicity of `interior` to obtain both components.
  have hxA : (x : X) ∈ interior (closure A) :=
    (interior_mono h_subsetA) hx
  have hxB : (x : X) ∈ interior (closure B) :=
    (interior_mono h_subsetB) hx
  exact And.intro hxA hxB