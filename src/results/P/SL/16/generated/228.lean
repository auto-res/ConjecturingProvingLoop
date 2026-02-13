

theorem Topology.closure_interior_closure_inter_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- `closure (A ∩ B) ⊆ closure A`
  have h_cl_subset_left : closure (A ∩ B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- Hence `interior (closure (A ∩ B)) ⊆ interior (closure A)`
  have h_int_subset_left :
      interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono h_cl_subset_left
  -- Taking closures preserves this inclusion
  have h_cl_int_subset_left :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure A)) :=
    closure_mono h_int_subset_left
  -- Obtain the left component of the goal
  have hx_left : x ∈ closure (interior (closure A)) :=
    h_cl_int_subset_left hx
  -- The corresponding statements for `B`
  have h_cl_subset_right : closure (A ∩ B) ⊆ closure B :=
    closure_mono Set.inter_subset_right
  have h_int_subset_right :
      interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono h_cl_subset_right
  have h_cl_int_subset_right :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure B)) :=
    closure_mono h_int_subset_right
  have hx_right : x ∈ closure (interior (closure B)) :=
    h_cl_int_subset_right hx
  -- Combine the two components
  exact And.intro hx_left hx_right