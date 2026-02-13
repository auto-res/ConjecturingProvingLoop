

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  have hCl : closure A ⊆ closure B := closure_mono hAB
  exact interior_mono hCl