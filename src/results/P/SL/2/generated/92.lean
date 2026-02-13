

theorem Topology.isOpen_subset_closure_implies_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A U : Set X} :
    IsOpen U → closure U ⊆ closure (A : Set X) →
      U ⊆ interior (closure (A : Set X)) := by
  intro hOpen hClosureSub
  -- First, note that every point of `U` lies in `closure U`, hence in `closure A`.
  have hU_sub_closureA : (U : Set X) ⊆ closure (A : Set X) := by
    intro x hxU
    have : x ∈ closure U := subset_closure hxU
    exact hClosureSub this
  -- Apply the maximality of `interior` with the open set `U`.
  exact interior_maximal hU_sub_closureA hOpen