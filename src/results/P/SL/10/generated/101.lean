

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  have h₂ : interior (closure A) ⊆ interior (closure B) := interior_mono h₁
  exact closure_mono h₂