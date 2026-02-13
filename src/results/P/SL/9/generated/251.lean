

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- `hx` gives membership in the closure of `A ∪ B`
  -- and non-membership in its interior.
  have hx_cl_union : x ∈ closure (A ∪ B : Set X) := hx.1
  have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := hx.2
  -- From `hx_not_int_union`, deduce non-membership in the interiors of `A` and `B`.
  have h_not_intA : x ∉ interior A := by
    intro hx_intA
    have h_subset : interior A ⊆ interior (A ∪ B) :=
      interior_mono (by
        intro y hy
        exact Or.inl hy)
    exact hx_not_int_union (h_subset hx_intA)
  have h_not_intB : x ∉ interior B := by
    intro hx_intB
    have h_subset : interior B ⊆ interior (A ∪ B) :=
      interior_mono (by
        intro y hy
        exact Or.inr hy)
    exact hx_not_int_union (h_subset hx_intB)
  -- Rewrite `closure (A ∪ B)` as the union of the closures.
  have h_eq : closure (A ∪ B : Set X) = closure A ∪ closure B :=
    (Topology.closure_union_eq (A := A) (B := B))
  have hx_cl_AB : x ∈ closure A ∪ closure B := by
    simpa [h_eq] using hx_cl_union
  -- Conclude that `x` lies in at least one of the desired frontiers.
  cases hx_cl_AB with
  | inl hx_clA =>
      exact Or.inl ⟨hx_clA, h_not_intA⟩
  | inr hx_clB =>
      exact Or.inr ⟨hx_clB, h_not_intB⟩