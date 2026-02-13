

theorem Topology.interiorClosureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
      have h_mono :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior A ⊆ interior (A ∪ B)`
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_subset : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_subset
        -- Step 2: take closures
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        -- Step 3: take interiors again
        exact interior_mono h_closure_subset
      exact h_mono hxA
  | inr hxB =>
      -- The argument is symmetric for `B`.
      have h_mono :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior B ⊆ interior (A ∪ B)`
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_subset : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact interior_mono h_subset
        -- Step 2: take closures
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        -- Step 3: take interiors again
        exact interior_mono h_closure_subset
      exact h_mono hxB