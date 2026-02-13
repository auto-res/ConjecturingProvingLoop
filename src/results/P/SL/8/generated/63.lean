

theorem P1_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  -- First, rewrite `P1 A` as an inclusion of closures.
  have h₁ : closure A ⊆ closure (interior A) :=
    (P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1
  -- Then, use the general inclusion `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  -- Compose the two inclusions to obtain the desired result.
  dsimp [Topology.P1]
  exact Set.Subset.trans h₁ h₂