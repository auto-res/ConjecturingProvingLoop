

theorem Topology.dense_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense (A : Set X)) (hB : Dense (B : Set X)) :
    Dense (A ∪ B : Set X) := by
  -- The closure of `A` is the whole space.
  have hA_closure : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
  -- Since `A ⊆ A ∪ B`, we have `closure A ⊆ closure (A ∪ B)`.
  have h_superset : (Set.univ : Set X) ⊆ closure (A ∪ B : Set X) := by
    have h₁ : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have h_subset : (A : Set X) ⊆ A ∪ B := by
        intro x hx; exact Or.inl hx
      exact closure_mono h_subset
    simpa [hA_closure] using h₁
  -- The reverse inclusion is trivial.
  have h_subset : closure (A ∪ B : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx; simp
  -- Therefore the closure of `A ∪ B` is the whole space.
  have h_closure_union : closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm h_subset h_superset
  -- Conclude that `A ∪ B` is dense.
  exact (dense_iff_closure_eq).2 h_closure_union