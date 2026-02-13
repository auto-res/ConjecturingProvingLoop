

theorem Topology.P1_of_P3_and_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (closure A ⊆ closure (interior A)) → Topology.P1 A := by
  intro hP3 hClSub
  intro x hxA
  -- From `P3`, the point `x` lies in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) := hP3 hxA
  -- We will show that `interior (closure A) ⊆ closure (interior A)`.
  have hIncl : (interior (closure A) : Set X) ⊆ closure (interior A) := by
    -- `interior (closure A)` is contained in `closure A`.
    have h₁ : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    -- Chain the inclusions using the hypothesis `closure A ⊆ closure (interior A)`.
    exact Set.Subset.trans h₁ hClSub
  -- Applying the inclusion to `x` gives the desired conclusion.
  exact hIncl hxIntCl