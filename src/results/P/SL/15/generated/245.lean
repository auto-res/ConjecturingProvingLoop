

theorem denseInterior_left_implies_P2_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense (interior A) → Topology.P2 (A ∪ B) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _hx
  -- `closure (interior A)` is the whole space.
  have h_closure_intA : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (A ∪ B)`
  have h_int_subset : interior A ⊆ interior (A ∪ B) := by
    have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
    exact interior_mono this
  -- hence `closure (interior A) ⊆ closure (interior (A ∪ B))`
  have h_closure_subset :
      (closure (interior A : Set X)) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_int_subset
  -- together with the previous equality we get `closure (interior (A ∪ B)) = univ`
  have h_closure_univ :
      closure (interior (A ∪ B) : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · simpa [h_closure_intA] using h_closure_subset
  -- therefore its interior is also the whole space
  have h_interior_univ :
      interior (closure (interior (A ∪ B))) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- conclude the desired membership
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_univ] using this