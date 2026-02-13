

theorem Topology.closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∩ interior (Aᶜ) = closure A ∩ (closure A)ᶜ := by
      simpa [h]
    _ = (∅ : Set X) := by
      simpa [Set.inter_compl_self]