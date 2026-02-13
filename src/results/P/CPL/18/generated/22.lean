

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Dense A) (hAB : A ⊆ B) : Topology.P3 B := by
  dsimp [Topology.P3]
  intro x hxB
  -- Show that `closure B = univ`.
  have h_closureB : closure (B : Set X) = (Set.univ : Set X) := by
    -- `closure A = univ` since `A` is dense.
    have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
      simpa using hA.closure_eq
    -- `closure A ⊆ closure B` because `A ⊆ B`.
    have h_subset : closure (A : Set X) ⊆ closure B := closure_mono hAB
    -- Hence `univ ⊆ closure B`.
    have h_subset' : (Set.univ : Set X) ⊆ closure B := by
      simpa [h_closureA] using h_subset
    -- Combine the inclusions to get equality.
    exact subset_antisymm (Set.subset_univ _) h_subset'
  -- With `closure B = univ`, the interior is also `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closureB, interior_univ] using this