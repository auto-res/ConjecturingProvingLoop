

theorem Topology.interior_inter_eq_empty_of_closure_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure A ∩ closure B = (∅ : Set X)) :
    interior (A ∩ B) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  ·
    -- First, show `interior (A ∩ B)` is contained in `closure A ∩ closure B`.
    have hsubset : interior (A ∩ B) ⊆ closure A ∩ closure B := by
      intro x hx
      have hxAB : x ∈ A ∩ B := interior_subset hx
      have hxA : x ∈ closure A := subset_closure hxAB.1
      have hxB : x ∈ closure B := subset_closure hxAB.2
      exact And.intro hxA hxB
    -- Rewriting with the hypothesis `h` gives the desired inclusion in `∅`.
    simpa [h] using hsubset
  ·
    exact Set.empty_subset _