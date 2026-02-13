

theorem P2_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- From `P2` we know the closures of `A` and `interior A` coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    P2_implies_closure_eq (A := A) hP2
  -- Prove the desired equality by showing mutual inclusions.
  apply Set.Subset.antisymm
  · -- First inclusion:
    -- `interior (closure A)` is contained in `closure (interior A)`.
    have hsubset : interior (closure A) ⊆ closure (interior A) := by
      intro x hx
      have hx_cl : (x : X) ∈ closure A := interior_subset hx
      simpa [hEq] using hx_cl
    -- Taking closures preserves this inclusion.
    simpa [closure_closure] using (closure_mono hsubset)
  · -- Second inclusion:
    -- `interior A` is contained in `interior (closure A)`.
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- Taking closures yields the required inclusion.
    exact closure_mono hsubset