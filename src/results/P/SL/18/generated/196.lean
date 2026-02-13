

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  have hxCl : x ∈ closure (A : Set X) :=
    (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  -- Apply the neighborhood characterization of `closure` with the open set `univ`.
  have hNonempty : ((Set.univ : Set X) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxCl Set.univ isOpen_univ (by
      -- `x` trivially belongs to `univ`.
      trivial)
  simpa [Set.inter_univ] using hNonempty