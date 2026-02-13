

theorem inter_interiors_subset_interior_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ interior B ⊆
      interior (closure ((A ∩ B) : Set X)) := by
  intro x hx
  -- First, `x` belongs to `interior (A ∩ B)`.
  have hx_int : (x : X) ∈ interior ((A ∩ B) : Set X) :=
    inter_interiors_subset_interior_inter (A := A) (B := B) hx
  -- Then use the inclusion `interior S ⊆ interior (closure S)`.
  have h_subset :
      interior ((A ∩ B) : Set X) ⊆
        interior (closure ((A ∩ B) : Set X)) :=
    interior_subset_interior_closure (A := A ∩ B)
  exact h_subset hx_int