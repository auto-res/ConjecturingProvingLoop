

theorem Topology.interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hxIntA
  -- Step 1: `x` lies in `interior (closure A)` because `A ⊆ closure A`.
  have hxIntClA : x ∈ interior (closure (A : Set X)) := by
    have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    have hMono : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono hSub
    exact hMono hxIntA
  -- Step 2: every point of `interior (closure A)` lies in its closure.
  exact subset_closure hxIntClA