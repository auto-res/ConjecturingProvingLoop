

theorem dense_of_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) = Set.univ →
      Dense (A : Set X) := by
  intro hUniv
  -- `closure (A)` contains the dense set `interior (closure A)`,
  -- whose closure is `univ` by hypothesis.
  have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hIncl :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (A := A)
    simpa [hUniv] using hIncl
  -- Hence `closure A = univ`.
  have hEq : closure (A : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact hSub
  -- Translate this equality into density of `A`.
  exact (Topology.dense_iff_closure_eq_univ (A := A)).2 hEq