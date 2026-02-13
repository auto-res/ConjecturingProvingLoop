

theorem Topology.closure_interior_inter_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA_subset : interior ((A ∩ B) : Set X) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB_subset : interior ((A ∩ B) : Set X) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  -- Monotonicity of `closure` transports the point into the respective closures
  have hxA : x ∈ closure (interior A) := (closure_mono hA_subset) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB_subset) hx
  exact ⟨hxA, hxB⟩