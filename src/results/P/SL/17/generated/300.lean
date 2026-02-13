

theorem Topology.frontier_closure_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense A) :
    frontier (closure A) = (∅ : Set X) := by
  -- `A` is dense, so its closure is the whole space.
  have hCl : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hCl] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Rewrite the frontier of `closure A` using an existing lemma.
  have hFront :
      frontier (closure A) =
        closure A \ interior (closure A) :=
    Topology.frontier_closure_eq_closure_diff_interior_closure (A := A)
  -- Combine the above equalities and simplify.
  calc
    frontier (closure A) =
        closure A \ interior (closure A) := hFront
    _ = (Set.univ : Set X) \ (Set.univ : Set X) := by
      simpa [hCl, hInt]
    _ = (∅ : Set X) := by
      simp