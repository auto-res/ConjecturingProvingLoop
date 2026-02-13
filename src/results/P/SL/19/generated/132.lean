

theorem Topology.interior_closure_inter_subset_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∪ interior (closure B) := by
  intro x hx
  have h : x ∈ interior (closure A) ∩ interior (closure B) :=
    (Topology.interior_closure_inter_subset (A := A) (B := B)) hx
  exact Or.inl h.1