

theorem P2_of_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X} : closure (interior B) = Set.univ → P2 (A ∪ B) := by
  intro h_dense
  -- First, compute that `interior (closure (interior (A ∪ B))) = univ`.
  have h_int_univ :
      interior (closure (interior (A ∪ B))) = (Set.univ : Set X) := by
    -- Show that the corresponding closure is the whole space.
    have h_closure_univ :
        closure (interior (A ∪ B)) = (Set.univ : Set X) := by
      -- `interior B ⊆ interior (A ∪ B)`
      have h_subset : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono this
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Use the hypothesis `closure (interior B) = univ`.
      have h_univ_subset :
          (Set.univ : Set X) ⊆ closure (interior (A ∪ B)) := by
        simpa [h_dense] using h_closure_subset
      -- Deduce equality via `subset_antisymm`.
      apply Set.Subset.antisymm
      · intro y hy; trivial
      · exact h_univ_subset
    -- Taking interiors, we still get `univ`.
    simpa [h_closure_univ, interior_univ]
  -- Now prove `P2 (A ∪ B)`.
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_univ] using this