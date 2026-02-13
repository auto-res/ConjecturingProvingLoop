

theorem P3_of_dense_subset {X} [TopologicalSpace X] {A B : Set X} (hsub : B ⊆ A) (hDense : Dense B) : P3 A := by
  -- `closure B` is the whole space since `B` is dense.
  have hB : closure (B : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- From `B ⊆ A`, we obtain `closure B ⊆ closure A`.
  have hsubset : (closure (B : Set X)) ⊆ closure (A : Set X) := closure_mono hsub
  -- Hence `closure A` is also the whole space.
  have hA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    simpa [hB] using hsubset
  -- Apply the existing lemma `P3_of_dense`.
  exact P3_of_dense (A := A) hA

theorem P2_singleton_of_discrete {X} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P2 ({x} : Set X) := by
  -- `{x}` is open in a discrete topology.
  have h_open : IsOpen ({x} : Set X) := by
    simpa using isOpen_discrete (s := ({x} : Set X))
  -- Apply the lemma for open sets.
  exact P2_of_open (A := {x}) h_open