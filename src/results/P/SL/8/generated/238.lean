

theorem P1_imp_closure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A ⊆ closure (interior (closure A)) := by
  -- First, translate `P1 A` into an inclusion between closures.
  have h₁ : closure A ⊆ closure (interior A) :=
    (Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1
  -- Next, widen the target from `closure (interior A)` to
  -- `closure (interior (closure A))` using monotonicity.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂