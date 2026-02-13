

theorem Topology.dense_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Dense (A ∪ B : Set X) := by
  intro hA_dense
  -- Since `A` is dense, its closure is the whole space.
  have hA_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hA_dense.closure_eq
  -- Hence `closure (A ∪ B)` contains `univ`, because it contains `closure A`.
  have h_superset : (Set.univ : Set X) ⊆ closure (A ∪ B : Set X) := by
    have h_incl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have h_subset : (A : Set X) ⊆ A ∪ B := by
        intro x hx; exact Or.inl hx
      exact closure_mono h_subset
    simpa [hA_closure] using h_incl
  -- The opposite inclusion is trivial.
  have h_subset : closure (A ∪ B : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx; simp
  -- Therefore `closure (A ∪ B) = univ`, so `A ∪ B` is dense.
  have h_closure_eq : closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm h_subset h_superset
  exact (dense_iff_closure_eq).2 h_closure_eq