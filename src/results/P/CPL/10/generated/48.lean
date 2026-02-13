

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod (Set.prod A B) C) := by
  -- First, obtain `P2` for the product `A ×ˢ B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine this with `C` to get the required triple product.
  simpa using
    (Topology.P2_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)

theorem P1_exists_finite {X : Type*} [TopologicalSpace X] : ∃ A : Set X, A.Finite ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), Set.finite_empty, ?_⟩
  intro x hx
  cases hx