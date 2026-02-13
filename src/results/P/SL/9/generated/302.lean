

theorem Topology.closureInteriors_inter_subset_closureInteriorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  -- `interior A` is contained in `interior (A ∪ B)`.
  have h_intA_subset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact interior_mono h_sub
  -- Hence their closures satisfy the same inclusion.
  have h_clA_subset :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_intA_subset
  -- Apply the inclusion to the first component of `hx`.
  exact h_clA_subset hx.1