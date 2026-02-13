

theorem P3_product_three_univ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (hA : Topology.P3 (A := (Set.univ : Set X))) (hB : Topology.P3 (A := (Set.univ : Set Y))) (hC : Topology.P3 (A := (Set.univ : Set Z))) : Topology.P3 (A := Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.univ : Set Z))) := by
  -- First, build `P3` for the product of the two universal sets in `Y` and `Z`.
  have hBC : Topology.P3 (A := Set.prod (Set.univ : Set Y) (Set.univ : Set Z)) := by
    simpa using
      (Topology.P3_prod
        (A := (Set.univ : Set Y))
        (B := (Set.univ : Set Z))
        hB hC)
  -- Now take the product with the universal set in `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y) (Set.univ : Set Z))
      hA hBC)

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : ∃ K, IsCompact K ∧ K ⊆ A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
    simpa [hA_empty] using (Set.empty_subset (A : Set X))
  · have hA_nonempty : (A : Set X).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨x, hxA⟩
    refine ⟨({x} : Set X), isCompact_singleton, ?_⟩
    intro y hy
    have : y = x := by
      simpa [Set.mem_singleton_iff] using hy
    simpa [this] using hxA