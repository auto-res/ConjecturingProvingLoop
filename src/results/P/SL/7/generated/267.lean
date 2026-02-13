

theorem Topology.interiorClosure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure (A : Set X)) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Taking closures preserves this inclusion.
  have hCl : closure (A \ B : Set X) ⊆ closure (A : Set X) := closure_mono hSub
  -- Applying monotonicity of `interior` gives the desired result.
  exact interior_mono hCl