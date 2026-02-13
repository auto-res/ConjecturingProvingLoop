

theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ frontier A ⊆ closure (interior A) := by
  -- First equivalence: `P1 A ↔ closure (interior A) = closure A`.
  have h₁ : Topology.P1 A ↔ closure (interior A) = closure A :=
    Topology.P1_iff_closure_interior_eq_closure (A := A)
  -- Second equivalence: `closure (interior A) = closure A ↔ frontier A ⊆ closure (interior A)`.
  have h₂ : closure (interior A) = closure A ↔ frontier A ⊆ closure (interior A) :=
    (Topology.frontier_subset_closure_interior_iff_closure_interior_eq_closure (A := A)).symm
  -- Combine the two equivalences.
  exact h₁.trans h₂