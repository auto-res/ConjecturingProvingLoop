

theorem Topology.P2_implies_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure (interior (closure (A : Set X)))) := by
  intro hP2
  intro x hxA
  -- From `P2`, we obtain that `x` lies in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  -- Use the monotonicity lemma to move further inside the nested closures.
  have hsubset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    Topology.interior_closure_interior_subset_interior_closure_interior_closure (A := A)
  exact hsubset hx₁