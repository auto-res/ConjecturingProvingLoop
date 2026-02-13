

theorem Topology.frontier_union_subset_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Decompose the hypothesis `hx` into its two components.
  have hx_cl_union : x ∈ closure (A ∪ B) := hx.1
  have hx_not_int_union : x ∉ interior (A ∪ B) := hx.2
  -- Because `A` and `B` are open, their union is open, hence its interior
  -- is just itself.
  have h_int_union : interior (A ∪ B) = A ∪ B := by
    have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
    simpa using h_open_union.interior_eq
  -- Translate the non‐interiority condition.
  have hx_not_union : x ∉ A ∪ B := by
    simpa [h_int_union] using hx_not_int_union
  -- Rewrite membership in the closure of the union.
  have hx_closure_split : x ∈ closure A ∪ closure B := by
    have h_eq := Topology.closure_union_eq (A := A) (B := B)
    simpa [h_eq] using hx_cl_union
  -- Break into cases.
  cases hx_closure_split with
  | inl hx_clA =>
      -- `x` lies in the closure of `A` but not in its interior,
      -- so `x` is in the frontier of `A`.
      have hx_not_intA : x ∉ interior A := by
        intro hx_intA
        have hxA : x ∈ A := interior_subset hx_intA
        exact hx_not_union (Or.inl hxA)
      exact Or.inl ⟨hx_clA, hx_not_intA⟩
  | inr hx_clB =>
      -- Symmetric argument for `B`.
      have hx_not_intB : x ∉ interior B := by
        intro hx_intB
        have hxB : x ∈ B := interior_subset hx_intB
        exact hx_not_union (Or.inr hxB)
      exact Or.inr ⟨hx_clB, hx_not_intB⟩