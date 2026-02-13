

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P1` for the product `B × C`.
  have hBC : Topology.P1 (Set.prod B C) := by
    simpa using
      (P1_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now, obtain `P1` for `A × (B × C)` using the previous result.
  simpa using
    (P1_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hA hBC)

theorem P2_if_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure (interior A))) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  simpa [h] using hx_closure

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  exact
    closure_mono
      (interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior)