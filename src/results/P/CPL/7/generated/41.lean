

theorem P3_of_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa using (h ▸ hx_cl)

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) : Topology.P2 A := by
  intro x hx
  -- `A` is open in a discrete space, hence `interior A = A`.
  have hA_open : IsOpen (A : Set X) := isOpen_discrete _
  have hx_intA : x ∈ interior A := by
    simpa [hA_open.interior_eq] using hx
  -- We have `A ⊆ closure (interior A)` (which equals `closure A`).
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    simpa [hA_open.interior_eq] using
      (subset_closure : (A : Set X) ⊆ closure A)
  -- Taking interiors preserves inclusions.
  have h_subset_int :
      interior A ⊆ interior (closure (interior A)) :=
    interior_mono h_subset
  exact h_subset_int hx_intA