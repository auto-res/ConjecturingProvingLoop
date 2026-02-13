

theorem interior_closure_inter_eq_empty_of_disjoint_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ closure (B : Set X) = (∅ : Set X) →
      interior (closure ((A ∩ B) : Set X)) = (∅ : Set X) := by
  intro hDisjoint
  apply Set.Subset.antisymm
  · intro x hx
    have hx_cl : (x : X) ∈ closure ((A ∩ B) : Set X) :=
      interior_subset hx
    have hx_inter :
        (x : X) ∈ closure (A : Set X) ∩ closure (B : Set X) :=
      (closure_inter_subset_inter_closures (A := A) (B := B)) hx_cl
    simpa [hDisjoint] using hx_inter
  · intro x hx
    cases hx