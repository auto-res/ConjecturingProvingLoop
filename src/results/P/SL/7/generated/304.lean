

theorem Topology.closureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior A) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C)) := by
  intro x hx
  -- `closure (interior A)` is contained in the target.
  have hAincl : closure (interior A) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inl (Or.inl hy)
  -- `closure (interior B)` is contained in the target.
  have hBincl : closure (interior B) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inl (Or.inr hy)
  -- `closure (interior C)` is contained in the target.
  have hCincl : closure (interior C) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inr hy
  -- Analyse the membership of `x`.
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA => exact hAincl hA
      | inr hB => exact hBincl hB
  | inr hC => exact hCincl hC