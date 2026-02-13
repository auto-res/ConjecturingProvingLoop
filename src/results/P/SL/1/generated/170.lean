

theorem Topology.interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- `closure B` is contained in `closure (A ∪ B)`.
  have hsubset : closure B ⊆ closure (A ∪ B) := by
    apply closure_mono
    exact Set.subset_union_right
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono hsubset) hx