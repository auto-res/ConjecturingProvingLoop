

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
      interior (closure ((A ∪ B) : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `interior (closure A)`
      -- We expand this to `interior (closure (A ∪ B))` using monotonicity.
      have hsub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have hcl : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono hsub
      have hint : interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hint hxA
  | inr hxB =>
      -- Symmetric argument for `B`.
      have hsub : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hcl : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono hsub
      have hint : interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hcl
      exact hint hxB