

theorem Topology.closure_union_interior_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∪ interior B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_subset hxA
  | inr hxB =>
      -- `x` lies in `interior B`, hence in `B`, and therefore in `A ∪ B`.
      have hx_union : (x : X) ∈ A ∪ B := Or.inr (interior_subset hxB)
      -- Every point of `A ∪ B` belongs to its closure.
      exact subset_closure hx_union