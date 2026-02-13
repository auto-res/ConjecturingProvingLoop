

theorem Topology.inter_closure_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  -- `x` lies in `closure (interior A)`.
  have hxA : x ∈ closure (interior A) := hx.1
  -- `interior A` is contained in `interior (A ∪ B)`.
  have h_int_subset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact interior_mono h_sub
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_int_subset
  -- Transport the membership of `x`.
  exact h_closure_subset hxA