

theorem Topology.interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  -- Step 1: enlarge `interior A` to `interior (A ∪ B)` using monotonicity of `interior`.
  have hx_union : x ∈ interior (A ∪ B) :=
    (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)) hx
  -- Step 2: every set is contained in the closure of itself.
  have h_closure :
      (interior (A ∪ B) : Set X) ⊆ closure (interior (A ∪ B)) :=
    subset_closure
  -- Step 3: assemble the two inclusions.
  exact h_closure hx_union