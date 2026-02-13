

set_option maxRecDepth 10000

theorem Topology.interior_subset_closure_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  -- `interior A` is contained in `interior (A ∪ B)` because `A ⊆ A ∪ B`.
  have h_int_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Therefore, `x` belongs to `interior (A ∪ B)`.
  have hx' : (x : X) ∈ interior (A ∪ B) := h_int_subset hx
  -- Every point of a set lies in its closure.
  exact subset_closure hx'