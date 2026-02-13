

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x` belongs to `closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    have hsubset : interior (A ∩ B) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
    exact (closure_mono hsubset) hx
  -- Show `x` belongs to `closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    have hsubset : interior (A ∩ B) ⊆ interior B :=
      interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
    exact (closure_mono hsubset) hx
  exact And.intro hxA hxB