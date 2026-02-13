

theorem P2_iff_P1_of_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense A) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hxA
    -- First, prove that `closure (interior A)` is the whole space.
    have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · -- Since `A ⊆ closure (interior A)` (from `P1`) and `A` is dense,
        -- we get `closure A = univ ⊆ closure (interior A)`.
        have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
          have hA_subset : (A : Set X) ⊆ closure (interior A) := hP1
          simpa [closure_closure] using closure_mono hA_subset
        simpa [h.closure_eq] using h_subset
    -- Hence the interior of this closure is also the whole space.
    have h_int_univ : interior (closure (interior A)) = (Set.univ : Set X) := by
      simpa [h_closure_int, interior_univ]
    -- Conclude the desired membership.
    have : x ∈ (Set.univ : Set X) := by
      exact Set.mem_univ x
    simpa [h_int_univ] using this