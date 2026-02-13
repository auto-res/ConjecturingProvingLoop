

theorem Topology.closure_eq_closureInterior_and_closureInteriorClosure_of_P1_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      Topology.P3 (X:=X) A →
        (closure (A : Set X) = closure (interior A)) ∧
          (closure (A : Set X) = closure (interior (closure A))) := by
  intro hP1 hP3
  have h₁ : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  have h₂ : closure (A : Set X) = closure (interior (closure A)) :=
    Topology.P3_implies_closure_eq_closureInteriorClosure (X := X) (A := A) hP3
  exact And.intro h₁ h₂