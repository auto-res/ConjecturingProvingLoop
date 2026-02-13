

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x ∈ interior (closure A)`
      -- Since `closure A ⊆ closure (A ∪ B)`, the monotonicity of `interior`
      -- sends `hA` into the desired set.
      have hSub : closure A ⊆ closure (A ∪ B) := closure_mono (by
        intro z hz; exact Or.inl hz)
      exact (interior_mono hSub) hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ interior (closure B)`.
      have hSub : closure B ⊆ closure (A ∪ B) := closure_mono (by
        intro z hz; exact Or.inr hz)
      exact (interior_mono hSub) hB