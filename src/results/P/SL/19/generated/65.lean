

theorem Topology.closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inl hz)
      have hClos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSub
      exact hClos hA
  | inr hB =>
      have hSub : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro z hz; exact Or.inr hz)
      have hClos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hSub
      exact hClos hB