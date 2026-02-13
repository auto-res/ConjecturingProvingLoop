

theorem Topology.P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1 x hxA
  -- From `P1 A`, the point `x` lies in `closure (interior A)`.
  have hx_closure_int : (x : X) ∈ closure (interior A) := hP1 hxA
  -- `interior A` is contained in `interior (closure A)` because `A ⊆ closure A`.
  have hInt_sub :
      (interior A : Set X) ⊆ interior (closure A) := by
    have hSub : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono hSub
  -- Taking closures preserves inclusions.
  have hCl_sub :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt_sub
  -- Combining the two, obtain the desired membership.
  exact hCl_sub hx_closure_int