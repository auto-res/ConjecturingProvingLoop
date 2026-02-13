

theorem Topology.interior_closure_inter_interior_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure (A ∩ B)) := by
  intro x hx
  -- Step 1:  `(A ∩ interior B) ⊆ (A ∩ B)`
  have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact And.intro hy.1 (interior_subset hy.2)
  -- Step 2:  Take closures on both sides of the inclusion.
  have hClos : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono hSub
  -- Step 3:  Apply monotonicity of `interior`.
  exact (interior_mono hClos) hx