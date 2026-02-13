

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x ∈ interior (closure (interior A))`
      -- We show that this set is contained in the right-hand side via monotonicity.
      have hSubInt : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inl hz)
      have hSubClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSubInt
      have hSubInter :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hSubClos
      exact hSubInter hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ interior (closure (interior B))`.
      have hSubInt : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inr hz)
      have hSubClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSubInt
      have hSubInter :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hSubClos
      exact hSubInter hB