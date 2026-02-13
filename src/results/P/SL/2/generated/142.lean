

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- Step 1: enlarge the inner `closure` using monotonicity.
  have hCl : (closure (A : Set X)) ⊆ closure (B : Set X) := closure_mono hAB
  -- Step 2: apply monotonicity of `interior`.
  have hInt :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (B : Set X)) :=
    interior_mono hCl
  -- Step 3: take closures again to obtain the desired inclusion.
  exact closure_mono hInt