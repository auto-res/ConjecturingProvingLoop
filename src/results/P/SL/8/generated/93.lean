

theorem closureInterior_union_subset_closureInteriorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `closure (interior A)`
      -- We enlarge the set step by step:
      -- `interior A ⊆ interior (A ∪ B)`
      have hInt : interior A ⊆ interior (A ∪ B) := by
        have hSub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hSub
      -- Taking closures yields the desired containment.
      have hCl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      exact hCl hxA
  | inr hxB =>
      -- Symmetric argument for `B`
      have hInt : interior B ⊆ interior (A ∪ B) := by
        have hSub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hSub
      have hCl : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      exact hCl hxB